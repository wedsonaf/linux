// SPDX-License-Identifier: GPL-2.0

use crate::{
    bindings, c_str, c_types, container_of, error::from_kernel_result, str::CStr, to_result, Error,
    Result, ScopeGuard,
};
use alloc::boxed::Box;
use core::{cell::UnsafeCell, fmt, marker::PhantomData, mem::ManuallyDrop, ops::Deref};

fn parent_ptr<T: TypeDetails>(obj: Option<&Object<T>>) -> *mut bindings::kobject {
    if let Some(p) = obj {
        T::to_kobj(&p.0)
    } else {
        core::ptr::null_mut()
    }
}

pub struct Set {
    ptr: *mut bindings::kset,
}

unsafe impl Sync for Set {}

impl Set {
    // TODO: Add version with kset_uevent_ops.
    pub fn try_new(name: &CStr, parent: Option<&Object<impl TypeDetails>>) -> Result<Self> {
        let ptr = unsafe {
            bindings::kset_create_and_add(name.as_char_ptr(), core::ptr::null(), parent_ptr(parent))
        };
        if ptr.is_null() {
            Err(Error::ENOMEM)
        } else {
            Ok(Self { ptr })
        }
    }

    pub fn try_new_object<T: TypeDetails>(
        &self,
        name: fmt::Arguments<'_>,
        data: T::CreateType,
    ) -> Result<Object<T>> {
        Object::try_new_internal::<()>(name, None, Some(self), data)
    }

    pub fn try_new_object_with_parent<T: TypeDetails>(
        &self,
        name: fmt::Arguments<'_>,
        parent: &Object<impl TypeDetails>,
        data: T::CreateType,
    ) -> Result<Object<T>> {
        Object::try_new_internal(name, Some(parent), Some(self), data)
    }
}

impl Drop for Set {
    fn drop(&mut self) {
        unsafe { bindings::kset_unregister(self.ptr) }
    }
}

pub type Attribute<T = ()> = <T as TypeDetails>::AttributeType;

#[repr(C)]
pub struct Attributes<T: TypeDetails, const N: usize> {
    ptrs: [*const bindings::attribute; N],
    sentinel: usize,
    _p: PhantomData<T>,
}

unsafe impl<T: TypeDetails, const N: usize> Sync for Attributes<T, N> {}

impl<T: TypeDetails, const N: usize> Attributes<T, N> {
    pub const fn new(attrs: [&'static Attribute<T>; N]) -> Self {
        let mut ret = Self {
            ptrs: [core::ptr::null(); N],
            sentinel: 0,
            _p: PhantomData,
        };

        let mut i = 0;
        while i < N {
            ret.ptrs[i] = unsafe {
                (attrs[i] as *const T::AttributeType as *const u8).offset(T::ATTR_OFFSET) as _
            };
            i += 1;
        }

        ret
    }
}

pub struct AttributeGroup<T: TypeDetails = ()> {
    group: bindings::attribute_group,
    _p: PhantomData<T>,
}

unsafe impl<T: TypeDetails> Sync for AttributeGroup<T> {}

impl<T: TypeDetails> AttributeGroup<T> {
    pub const fn new<const N: usize>(
        name: Option<&'static CStr>,
        attrs: &'static Attributes<T, N>,
    ) -> Self {
        Self {
            group: bindings::attribute_group {
                name: if let Some(s) = name {
                    s.as_char_ptr()
                } else {
                    core::ptr::null()
                },
                is_visible: None,
                is_bin_visible: None,
                attrs: &attrs.ptrs[0] as *const _ as _,
                bin_attrs: core::ptr::null_mut(),
            },
            _p: PhantomData,
        }
    }
}

pub struct AttributeGroupsUnsized<'a, T: TypeDetails> {
    ptrs: *const *const bindings::attribute_group,
    _p: PhantomData<&'a T>,
}

impl<T: TypeDetails + 'static> AttributeGroupsUnsized<'static, T> {
    const EMPTY: Self = Self {
        ptrs: core::ptr::null(),
        _p: PhantomData,
    };
    pub const fn empty() -> AttributeGroupsUnsized<'static, T> {
        Self::EMPTY
    }
}

#[repr(C)]
pub struct AttributeGroups<T: TypeDetails, const N: usize> {
    ptrs: [*const bindings::attribute_group; N],
    sentinel: usize,
    _p: PhantomData<T>,
}

unsafe impl<T: TypeDetails, const N: usize> Sync for AttributeGroups<T, N> {}

impl<T: TypeDetails, const N: usize> AttributeGroups<T, N> {
    pub const fn new(groups: [&'static AttributeGroup<T>; N]) -> Self {
        let mut ret = Self {
            ptrs: [core::ptr::null(); N],
            sentinel: 0,
            _p: PhantomData,
        };

        let mut i = 0;
        while i < N {
            ret.ptrs[i] = &groups[i].group;
            i += 1;
        }

        ret
    }

    pub const fn groups(&self) -> AttributeGroupsUnsized<'_, T> {
        AttributeGroupsUnsized {
            ptrs: &self.ptrs[0],
            _p: PhantomData,
        }
    }
}

#[repr(C)]
pub struct WrappedObject<T: ?Sized> {
    kobj: UnsafeCell<bindings::kobject>,
    data: T,
}

unsafe impl<T: ?Sized + Sync> Sync for WrappedObject<T> {}

impl<T> WrappedObject<T> {
    pub fn new(data: T) -> Self {
        Self {
            // bindings::kboject must be zero-initialised.
            kobj: UnsafeCell::new(bindings::kobject::default()),
            data,
        }
    }
}

#[repr(C)]
pub struct WrappedAttribute<T: ?Sized = ()> {
    attr: bindings::attribute,
    data: T,
}

unsafe impl<T: ?Sized + Sync> Sync for WrappedAttribute<T> {}

impl<T> WrappedAttribute<T> {
    pub const fn new(name: &'static CStr, mode: u16, data: T) -> Self {
        Self {
            attr: bindings::attribute {
                name: name.as_char_ptr(),
                mode,
            },
            data,
        }
    }

    pub fn name(&self) -> &CStr {
        unsafe { CStr::from_char_ptr(self.attr.name) }
    }
}

impl<T> Deref for WrappedAttribute<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.data
    }
}

pub trait Type: Sized + 'static {
    // TODO: Allow implementations to customise alloc/free if they so choose.
    type AttributeExtraInfo = ();

    const ATTRIBUTE_GROUPS: AttributeGroupsUnsized<'static, Self> = AttributeGroupsUnsized::empty();

    /// Returns the contents of the attribute via the `out` parameter.
    fn show(
        _obj: &Object<Self>,
        _attr: &WrappedAttribute<Self::AttributeExtraInfo>,
        _out: &mut impl core::fmt::Write,
    ) -> Result {
        Err(Error::EIO)
    }

    /// Changes the contents of the attributes to the value stored in `contents`.
    fn store(
        _obj: &Object<Self>,
        _attr: &WrappedAttribute<Self::AttributeExtraInfo>,
        _contents: &[u8],
    ) -> Result<usize> {
        Err(Error::EIO)
    }
}

pub unsafe trait TypeAllocator: Sized {
    /// Allocates memory for a new object of this type.
    fn allocate_object(data: Self) -> Result<*const WrappedObject<Self>>;

    /// Frees memory previously allocated with [`TypeAllocator::allocate_object`].
    ///
    /// # Safety
    ///
    /// `obj` must have been returned by [`TypeAllocator::allocate_object`] with no previous call
    /// to [`TypeAllocator::free_object`] (i.e., it must only be freed once).
    unsafe fn free_object(obj: *const WrappedObject<Self>);
}

unsafe impl<T: Type> TypeAllocator for T {
    default fn allocate_object(data: Self) -> Result<*const WrappedObject<Self>> {
        let obj = Box::try_new(WrappedObject::new(data))?;
        Ok(Box::into_raw(obj))
    }

    default unsafe fn free_object(obj: *const WrappedObject<Self>) {
        unsafe { Box::from_raw(obj as *mut WrappedObject<Self>) };
    }
}

unsafe impl<T: Type + TypeAllocator> TypeDetails for T {
    type AttributeType = WrappedAttribute<T::AttributeExtraInfo>;
    type OuterType = WrappedObject<T>;
    type DerefType = T;
    type StoreType = *const WrappedObject<T>;
    type CreateType = T;

    const ATTR_OFFSET: isize = crate::offset_of!(WrappedAttribute<T::AttributeExtraInfo>, attr);

    unsafe fn clone_already_referenced(obj: &Self::StoreType) -> Self::StoreType {
        *obj
    }

    unsafe fn adopt_reference(ptr: *const Self::OuterType) -> Self::StoreType {
        ptr
    }

    fn to_kobj(obj: &Self::StoreType) -> *mut bindings::kobject {
        unsafe { (**obj).kobj.get() }
    }

    fn deref_kobj(obj: &Self::StoreType) -> &Self::DerefType {
        unsafe { &(**obj).data }
    }

    fn allocate_kobj(data: Self::CreateType) -> Result<Self::StoreType> {
        let obj = T::allocate_object(data)?;
        unsafe { bindings::kobject_init(Self::to_kobj(&obj), &Ktype::<T>::KTYPE as *const _ as _) };
        Ok(obj)
    }
}

struct Ktype<T: Type + TypeAllocator + TypeDetails>(core::marker::PhantomData<T>);

impl<T: Type + TypeAllocator + TypeDetails<StoreType = *const WrappedObject<T>>> Ktype<T> {
    const SYSFS_OPS: bindings::sysfs_ops = bindings::sysfs_ops {
        show: Some(Self::show_callback),
        store: Some(Self::store_callback),
    };

    const KTYPE: bindings::kobj_type = bindings::kobj_type {
        release: Some(Self::release_callback),
        sysfs_ops: &Self::SYSFS_OPS,
        default_attrs: core::ptr::null_mut(),
        default_groups: T::ATTRIBUTE_GROUPS.ptrs as _,
        child_ns_type: None,
        namespace: None,
        get_ownership: None,
    };

    unsafe extern "C" fn release_callback(kobj: *mut bindings::kobject) {
        let obj = container_of!(kobj, WrappedObject<T>, kobj);
        // SAFETY: The object was previously allocated with `T::allocate_object`.
        unsafe { T::free_object(obj) };
    }

    unsafe extern "C" fn show_callback(
        kobj: *mut bindings::kobject,
        attr: *mut bindings::attribute,
        buf: *mut c_types::c_char,
    ) -> isize {
        from_kernel_result! {
            // SAFETY: The C contract guarantees that `buf` is valid for write and at least
            // `PAGE_SIZE` bytes in length.
            let mut out = unsafe { crate::buffer::Buffer::from_raw(buf as _, crate::PAGE_SIZE) };

            let uattr = container_of!(attr, WrappedAttribute<T::AttributeExtraInfo>, attr);
            let obj = ManuallyDrop::new(Object::<T>(container_of!(kobj, WrappedObject<T>, kobj)));
            T::show(&obj, unsafe { &*uattr }, &mut out)?;
            Ok(out.bytes_written() as _)
        }
    }

    unsafe extern "C" fn store_callback(
        kobj: *mut bindings::kobject,
        attr: *mut bindings::attribute,
        buf: *const c_types::c_char,
        count: usize,
    ) -> isize {
        from_kernel_result! {
            // SAFETY: The C contract guarantees that `buf` is valid for read and at least `count`
            // bytes in length.
            let contents = unsafe { core::slice::from_raw_parts(buf as *const u8, count) };

            let uattr = crate::container_of!(attr, WrappedAttribute<T::AttributeExtraInfo>, attr);
            let obj = ManuallyDrop::new(Object::<T>(container_of!(kobj, WrappedObject<T>, kobj)));
            let written = T::store(&obj, unsafe { &*uattr }, contents)?;
            Ok(written as _)
        }
    }
}

/// A kobject type.
///
/// These are implied by the kobject's `ktype` field, which is a runtime-only piece of information
/// in C but known to the compiler in Rust.
// TODO: Add safety requirements: it needs to include the fact the `to_kobj` must return an
// embedded object as opposed to some arbitrary one.
pub unsafe trait TypeDetails {
    /// Contains details about attribute of this type.
    ///
    /// This is because different kobject types have different requirements, for example, devices
    /// require attributes to be embedded in a `device_attribute` struct while dynamic kobjects
    /// (created via `kobject_create`) require attributes to be embeeded in a 'kobj_attribute'
    /// struct. In C, functions like `sysfs_create_file` only require a `struct attribute` to be
    /// passed in.
    type AttributeType;
    type OuterType;
    type DerefType;
    type StoreType;
    type CreateType = Impossible;

    /// Offset from the beginning of [`Self::AttributeType`] to the inner `struct attribute`.
    const ATTR_OFFSET: isize;

    // TODO: We need the caller to ensure that the reference is indeed incremented.
    unsafe fn clone_already_referenced(obj: &Self::StoreType) -> Self::StoreType;

    // TODO: Review if we really want/need this.
    unsafe fn adopt_reference(ptr: *const Self::OuterType) -> Self::StoreType;

    fn to_kobj(obj: &Self::StoreType) -> *mut bindings::kobject;

    fn deref_kobj(obj: &Self::StoreType) -> &Self::DerefType;

    fn allocate_kobj(_data: Self::CreateType) -> Result<Self::StoreType> {
        Err(Error::ENOTSUPP)
    }
}

// TODO: We need to cover the case when a device is embedded in another structure, for example,
// amba_device being a device.
pub struct Device(*const bindings::device);
unsafe impl TypeDetails for Device {
    type AttributeType = bindings::device_attribute;
    type OuterType = bindings::device;
    type DerefType = Self;
    type StoreType = Self;

    const ATTR_OFFSET: isize = crate::offset_of!(Self::AttributeType, attr);

    unsafe fn adopt_reference(ptr: *const Self::OuterType) -> Self {
        Self(ptr)
    }

    unsafe fn clone_already_referenced(obj: &Self) -> Self {
        Self(obj.0)
    }

    fn to_kobj(obj: &Self) -> *mut bindings::kobject {
        (unsafe { core::ptr::addr_of!((*obj.0).kobj) }) as _
    }

    fn deref_kobj(obj: &Self::StoreType) -> &Self::DerefType {
        obj
    }
}

impl Device {
    /// Returns the name of the device.
    fn name(&self) -> &CStr {
        // SAFETY: `ptr` is valid because `self` keeps it alive.
        let name = unsafe { bindings::dev_name(self.0) };

        // SAFETY: The name of the device remains valid while it is alive (because the device is
        // never renamed, per the safety requirement of this trait). This is guaranteed to be the
        // case because the reference to `self` outlives the one of the returned `CStr` (enforced
        // by the compiler because of their lifetimes).
        unsafe { CStr::from_char_ptr(name) }
    }
}

#[repr(transparent)]
pub struct DynamicObjectAttribute(bindings::kobj_attribute);

unsafe impl Sync for DynamicObjectAttribute {}

impl DynamicObjectAttribute {
    pub const fn new<T: ObjectAttributeOps>(name: &'static CStr, mode: u16) -> Self {
        Self(bindings::kobj_attribute {
            attr: bindings::attribute {
                name: name.as_char_ptr(),
                mode,
            },
            show: Some(ObjectTable::<T>::show_callback),
            store: Some(ObjectTable::<T>::store_callback),
        })
    }

    pub fn name(&self) -> &CStr {
        unsafe { CStr::from_char_ptr(self.0.attr.name) }
    }
}

pub trait ObjectAttributeOps {
    fn show(_obj: &Object, _attr: &Attribute, _out: &mut impl core::fmt::Write) -> Result {
        Err(Error::EIO)
    }

    fn store(_obj: &Object, _attr: &Attribute, _contents: &[u8]) -> Result<usize> {
        Err(Error::EIO)
    }
}

struct ObjectTable<T: ObjectAttributeOps>(T);
impl<T: ObjectAttributeOps> ObjectTable<T> {
    unsafe extern "C" fn show_callback(
        kobj: *mut bindings::kobject,
        attr: *mut bindings::kobj_attribute,
        buf: *mut c_types::c_char,
    ) -> isize {
        from_kernel_result! {
            // SAFETY: The C contract guarantees that `buf` is valid for write and at least
            // `PAGE_SIZE` bytes in length.
            let mut out = unsafe { crate::buffer::Buffer::from_raw(buf as _, crate::PAGE_SIZE) };

            let dattr = container_of!(attr, DynamicObjectAttribute, 0.attr);
            let obj = ManuallyDrop::new(Object(kobj as _));

            T::show(&obj, unsafe { &*dattr }, &mut out)?;
            Ok(out.bytes_written() as _)
        }
    }

    unsafe extern "C" fn store_callback(
        kobj: *mut bindings::kobject,
        attr: *mut bindings::kobj_attribute,
        buf: *const c_types::c_char,
        count: usize,
    ) -> isize {
        from_kernel_result! {
            // SAFETY: The C contract guarantees that `buf` is valid for read and at least `count`
            // bytes in length.
            let contents = unsafe { core::slice::from_raw_parts(buf as *const u8, count) };

            let dattr = container_of!(attr, DynamicObjectAttribute, 0.attr);
            let obj = ManuallyDrop::new(Object(kobj as _));
            let written = T::store(&obj, unsafe { &*dattr }, contents)?;
            Ok(written as _)
        }
    }
}

unsafe impl Sync for Object<()> {}

unsafe impl TypeDetails for () {
    type AttributeType = DynamicObjectAttribute;
    type OuterType = bindings::kobject;
    type DerefType = Self;
    type StoreType = *const bindings::kobject;
    type CreateType = ();

    const ATTR_OFFSET: isize = crate::offset_of!(bindings::kobj_attribute, attr);

    unsafe fn clone_already_referenced(obj: &Self::StoreType) -> Self::StoreType {
        *obj
    }

    unsafe fn adopt_reference(ptr: *const Self::OuterType) -> Self::StoreType {
        ptr
    }

    fn to_kobj(obj: &Self::StoreType) -> *mut bindings::kobject {
        *obj as _
    }

    fn deref_kobj(_obj: &Self::StoreType) -> &Self::DerefType {
        &()
    }

    fn allocate_kobj(_data: Self::CreateType) -> Result<Self::StoreType> {
        let kobj = unsafe { bindings::kobject_create() };
        if kobj.is_null() {
            Err(Error::ENOMEM)
        } else {
            Ok(kobj)
        }
    }
}

pub enum Action {
    Add = bindings::kobject_action_KOBJ_ADD as _,
    Remove = bindings::kobject_action_KOBJ_REMOVE as _,
    Change = bindings::kobject_action_KOBJ_CHANGE as _,
    Move = bindings::kobject_action_KOBJ_MOVE as _,
    Online = bindings::kobject_action_KOBJ_ONLINE as _,
    Offline = bindings::kobject_action_KOBJ_OFFLINE as _,
    Bind = bindings::kobject_action_KOBJ_BIND as _,
    Unbind = bindings::kobject_action_KOBJ_UNBIND as _,
}

/// Wraps the kernel's `struct kobject`.
///
/// # Invariants
///
/// The pointer `Object::0` is non-null and valid. Its reference count is also non-zero.
pub struct Object<T: TypeDetails = ()>(T::StoreType);

unsafe impl<T: TypeDetails<OuterType = WrappedObject<U>>, U> Sync for Object<T> where U: Sync {}

impl<T: TypeDetails> Object<T> {
    pub fn try_new(name: fmt::Arguments<'_>, data: T::CreateType) -> Result<Self> {
        Self::try_new_internal::<()>(name, None, None, data)
    }

    pub fn try_new_with_parent(
        name: fmt::Arguments<'_>,
        parent: &Object<impl TypeDetails>,
        data: T::CreateType,
    ) -> Result<Self> {
        Self::try_new_internal(name, Some(parent), None, data)
    }

    fn try_new_internal<U: TypeDetails>(
        name: fmt::Arguments<'_>,
        parent: Option<&Object<U>>,
        set: Option<&Set>,
        data: T::CreateType,
    ) -> Result<Self> {
        let parent_ptr = parent_ptr(parent);
        let obj = T::allocate_kobj(data)?;
        let kobj = T::to_kobj(&obj);
        if let Some(s) = set {
            unsafe { (*kobj).kset = s.ptr };
        }
        let put_obj = ScopeGuard::new(|| unsafe { bindings::kobject_put(kobj) });
        to_result(|| unsafe {
            bindings::kobject_add(
                kobj,
                parent_ptr,
                c_str!("%pA").as_char_ptr(),
                &name as *const _ as *const c_types::c_void,
            )
        })?;
        put_obj.dismiss();
        Ok(Self(obj))
    }

    // TODO: gregkh tells me that we don't want to support manual creation of attributes.
    // TODO: For now, it's a static lifetime, but we can and should make it a PointerWrapper.
    // We should also make this return something.
    /*
    pub fn create_file(&self, outer_attr: &'static Attribute<T>) -> Result {
        let kobj = T::to_kobj(&self.0);
        let attr = T::to_attr(outer_attr);
        to_result(|| unsafe { bindings::sysfs_create_file_ns(kobj, attr, core::ptr::null()) })
    }

    pub fn create_files<const N: usize>(&self, attrs: &Attributes<T, N>) -> Result {
        let kobj = T::to_kobj(&self.0);
        let pattrs = &attrs.ptrs[0];
        to_result(|| unsafe { bindings::sysfs_create_files(kobj, pattrs) })
    }
    */

    // TODO: For now we leave this.
    pub fn create_group(&self, group: &AttributeGroup<T>) -> Result {
        let kobj = T::to_kobj(&self.0);
        to_result(|| unsafe { bindings::sysfs_create_group(kobj, &group.group) })
    }

    pub fn uevent(&self, action: Action) -> Result {
        let kobj = T::to_kobj(&self.0);
        to_result(|| unsafe { bindings::kobject_uevent(kobj, action as _) })
    }
}

impl<T: TypeDetails> Deref for Object<T> {
    type Target = T::DerefType;

    fn deref(&self) -> &Self::Target {
        T::deref_kobj(&self.0)
    }
}

impl<T: TypeDetails> Clone for Object<T> {
    fn clone(&self) -> Self {
        unsafe { bindings::kobject_get(T::to_kobj(&self.0)) };
        Self(unsafe { T::clone_already_referenced(&self.0) })
    }
}

impl<T: TypeDetails> Drop for Object<T> {
    fn drop(&mut self) {
        unsafe { bindings::kobject_put(T::to_kobj(&self.0)) }
    }
}

/// A wrapper for [`Object`] that doesn't automatically decrement the refcount when dropped.
///
/// We need the wrapper because [`ManuallyDrop`] alone would allow callers to call
/// [`ManuallyDrop::into_inner`]. This would allow an unsafe sequence to be triggered without
/// `unsafe` blocks because it would trigger an unbalanced call to `kobject_put`.
///
/// # Invariants
///
/// The wrapped [`Object`] remains valid for the lifetime of the object.
pub struct ObjectRef<'a, T: TypeDetails = ()> {
    inner: ManuallyDrop<Object<T>>,
    _p: PhantomData<&'a ()>,
}

impl<T: TypeDetails> ObjectRef<'_, T> {
    /// Constructs a new [`struct kobject`] wrapper that doesn't change its reference count.
    ///
    /// # Safety
    ///
    /// The pointer `ptr` must be non-null and valid for the lifetime of the object. The type of
    /// the object must also be compatible with `T`.
    pub unsafe fn from_ptr(ptr: *const T::OuterType) -> Self {
        Self {
            inner: ManuallyDrop::new(Object(unsafe { T::adopt_reference(ptr) })),
            _p: PhantomData,
        }
    }
}

impl<T: TypeDetails> Deref for ObjectRef<'_, T> {
    type Target = Object<T>;

    fn deref(&self) -> &Self::Target {
        self.inner.deref()
    }
}

/// Returns the `/sys/kernel` kobject.
pub fn kernel() -> ObjectRef<'static> {
    unsafe { ObjectRef::from_ptr(bindings::kernel_kobj) }
}

/// Returns the `/sys/kernel/mm` kobject.
pub fn mm() -> ObjectRef<'static> {
    unsafe { ObjectRef::from_ptr(bindings::mm_kobj) }
}

/// Returns the `/sys/firmware` kobject.
pub fn firmware() -> ObjectRef<'static> {
    unsafe { ObjectRef::from_ptr(bindings::firmware_kobj) }
}

#[non_exhaustive]
pub struct Impossible;

#[macro_export]
macro_rules! fmt {
    ($($args:tt)*) => {
        core::format_args!($($args)*)
    }
}
