// SPDX-License-Identifier: GPL-2.0

//! Linked lists.

pub use crate::unsafe_list::{Cursor, Iterator};
use crate::{types::TypedPointerWrapper, unsafe_list, ScopeGuard, True};
use core::{
    ptr::NonNull,
    sync::atomic::{AtomicBool, Ordering},
};

/// Implements the [`Adapter`] trait for a type where its [`Links`] instance is a field.
///
/// # Examples
///
/// ```
/// # use kernel::linked_list::Links;
///
/// struct Example {
///     links: Links<Example>,
/// }
///
/// kernel::impl_self_list_adapter!(Example, links);
/// ```
#[macro_export]
macro_rules! impl_self_list_adapter {
    ($entry_type:ty, $($field:tt)*) => {
        $crate::impl_custom_self_list_adapter!($entry_type, |obj| &obj.$($field)*);
    }
}

/// Implements the [`Adapter`] trait for a type where its [`Links`] instance is defined by an
/// expression.
///
/// # Examples
///
/// ```
/// # use kernel::linked_list::Links;
///
/// trait Example {
///     fn to_links(&self) -> &Links<dyn Example>;
/// }
///
/// kernel::impl_custom_self_list_adapter!(dyn Example, |obj| obj.to_links());
/// ```
#[macro_export]
macro_rules! impl_custom_self_list_adapter {
    ($entry_type:ty, $closure:expr) => {
        impl $crate::linked_list::Adapter for $entry_type {
            type EntryType = Self;
            fn to_links(obj: &Self) -> &$crate::linked_list::Links<Self> {
                let closure: fn(&Self) -> &$crate::linked_list::Links<Self> = $closure;
                closure(obj)
            }
        }
    };
}

/// An adapter for a linked list.
///
/// Most users won't have to implement this, instead they will implement [`Adapter`] for the
/// wrapped type and leverage an existing implementation of [`WrappedAdapter`], like for
/// [`crate::sync::Ref<T>`] and [`alloc::boxed::Box<T>`].
pub trait WrappedAdapter {
    /// The type that owns the list entry. This is typically [`alloc::boxed::Box<T>`] or
    /// [`crate::sync::Ref<T>`].
    type OwnedType: TypedPointerWrapper;

    /// Retrieves the linked list links for the given object.
    fn to_links(
        obj: &<Self::OwnedType as TypedPointerWrapper>::Target,
    ) -> &Links<<Self::OwnedType as TypedPointerWrapper>::Target>;
}

impl<T: TypedPointerWrapper> WrappedAdapter for T
where
    T::Target: Adapter<EntryType = T::Target>,
{
    type OwnedType = T;

    fn to_links(
        obj: &<Self::OwnedType as TypedPointerWrapper>::Target,
    ) -> &Links<<Self::OwnedType as TypedPointerWrapper>::Target> {
        <T::Target as Adapter>::to_links(obj)
    }
}

impl<A: WrappedAdapter + ?Sized> Adapter for A {
    type EntryType = <A::OwnedType as TypedPointerWrapper>::Target;
    fn to_links(obj: &Self::EntryType) -> &Links<Self::EntryType> {
        <A as WrappedAdapter>::to_links(obj)
    }
}

/// A linked-list adapter.
///
/// Its a separate type (as opposed to implemented by the type of the elements of the list) so that
/// a given type can be inserted into multiple lists at the same time; in such cases, each list
/// needs its own adapter that returns a different pointer to links.
pub trait Adapter {
    /// The type of the enties in the list.
    type EntryType: ?Sized;

    /// Retrieves the linked list links for the given object.
    fn to_links(obj: &Self::EntryType) -> &Links<Self::EntryType>;
}

unsafe impl<T: Adapter + ?Sized> unsafe_list::Adapter for T {
    type EntryType = T::EntryType;
    fn to_links(obj: &Self::EntryType) -> &unsafe_list::Links<Self::EntryType> {
        &<T as Adapter>::to_links(obj).inner
    }
}

/// The links used to link an object in a linked list.
///
/// Instances of this type are usually embedded in structures and returned in calls to
/// [`Adapter::to_links`].
pub struct Links<T: ?Sized> {
    inserted: AtomicBool,
    inner: unsafe_list::Links<T>,
}

impl<T: ?Sized> Links<T> {
    /// Constructs a new [`Links`] instance that isn't in any lists yet.
    pub fn new() -> Self {
        Self {
            inserted: AtomicBool::new(false),
            inner: unsafe_list::Links::new(),
        }
    }

    fn acquire_for_insertion(&self) -> bool {
        self.inserted
            .compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed)
            .is_ok()
    }

    fn release_after_removal(&self) {
        self.inserted.store(false, Ordering::Release);
    }
}

impl<T: ?Sized> Default for Links<T> {
    fn default() -> Self {
        Self::new()
    }
}

/// A linked list.
///
/// Elements in the list are wrapped and ownership is transferred to the list while the element is
/// in the list.
///
/// # Examples
///
/// This example is a list of boxed entries, which are also mutable:
///
/// ```
/// # use kernel::linked_list::{Links, List};
/// use alloc::boxed::Box;
///
/// struct Example {
///     value: usize,
///     links: Links<Example>,
/// }
///
/// kernel::impl_self_list_adapter!(Example, links);
///
/// let mut list = List::<Box<Example>>::new();
/// list.push_back(Box::try_new(Example { value: 10, links: Links::new() }).unwrap());
/// list.push_back(Box::try_new(Example { value: 20, links: Links::new() }).unwrap());
///
/// list.cursor_front_mut().current().unwrap().value = 30;
/// list.cursor_back_mut().current().unwrap().value = 40;
///
/// assert_eq!(list.pop_front().unwrap().value, 30);
/// assert_eq!(list.pop_front().unwrap().value, 40);
/// assert!(list.pop_front().is_none());
/// ```
///
/// This example is a list of ref-counted entries, which are shared and thus immutable:
///
/// ```
/// # use kernel::linked_list::{Links, List};
/// use kernel::sync::Ref;
///
/// struct Example {
///     links: Links<Example>,
/// }
///
/// kernel::impl_self_list_adapter!(Example, links);
///
/// let x = Ref::try_new(Example { links: Links::new() }).unwrap();
/// let y = Ref::try_new(Example { links: Links::new() }).unwrap();
///
/// let mut list = List::<Ref<Example>>::new();
/// list.push_back(x.clone());
/// list.push_back(y.clone());
///
/// assert!(core::ptr::eq(&*x, list.cursor_front().current().unwrap()));
/// assert!(core::ptr::eq(&*y, list.cursor_back().current().unwrap()));
/// ```
pub struct List<A: WrappedAdapter + ?Sized> {
    list: unsafe_list::List<A>,
}

impl<A: WrappedAdapter + ?Sized> List<A> {
    /// Constructs a new empty linked list.
    pub fn new() -> Self {
        Self {
            list: unsafe_list::List::new(),
        }
    }

    /// Returns whether the list is empty.
    pub fn is_empty(&self) -> bool {
        self.list.is_empty()
    }

    fn prepare_then_insert(
        &mut self,
        owned: A::OwnedType,
        insert: impl FnOnce(&mut unsafe_list::List<A>, &<A::OwnedType as TypedPointerWrapper>::Target),
    ) {
        let ptr = A::OwnedType::into_pointer(owned);
        // SAFETY: We just called `into_pointer` above.
        let guard = ScopeGuard::new(|| {
            unsafe { A::OwnedType::from_pointer(ptr) };
        });

        // SAFETY: The object is valid, as we just converted it into a pointer above.
        let target = unsafe { ptr.as_ref() };

        let links = A::to_links(target);
        if links.acquire_for_insertion() {
            insert(&mut self.list, target);
            guard.dismiss();
        }
    }

    /// Adds the given object to the end (back) of the list.
    ///
    /// It is dropped if it's already on this (or another) list; this can happen for
    /// reference-counted objects, so dropping means decrementing the reference count.
    pub fn push_back(&mut self, new: A::OwnedType) {
        self.prepare_then_insert(new, |list, target| {
            // SAFETY: We ensured the object was not in any lists with the call to
            // `acquire_for_insertion` above. The object will remain alive because of the call to
            // `into_pointer` above, which will keep it alive. We have a reference to the object,
            // either an exclusive or a shared one; in either case no other thread can change it.
            unsafe { list.push_back(target) };
        });
    }

    /// Inserts the given object after `existing`.
    ///
    /// It is dropped if it's already on this (or another) list; this can happen for
    /// reference-counted objects, so dropping means decrementing the reference count.
    ///
    /// # Safety
    ///
    /// Callers must ensure that `existing` points to a valid entry that is on the list.
    pub unsafe fn insert_after(
        &mut self,
        existing: NonNull<<A::OwnedType as TypedPointerWrapper>::Target>,
        new: A::OwnedType,
    ) {
        self.prepare_then_insert(new, |list, target| {
            // SAFETY: We ensured the object was not in any lists with the call to
            // `acquire_for_insertion` above. The object will remain alive because of the call to
            // `into_pointer` above, which will keep it alive. We have a reference to the object,
            // either an exclusive or a shared one; in either case no other thread can change it.
            unsafe { list.insert_after(existing, target) };
        });
    }

    /// Removes the given entry.
    ///
    /// # Safety
    ///
    /// Callers must ensure that `data` is either on this list or in no list. It being on another
    /// list leads to memory unsafety.
    pub unsafe fn remove(
        &mut self,
        data: &<A::OwnedType as TypedPointerWrapper>::Target,
    ) -> Option<A::OwnedType> {
        if !A::to_links(data).inserted.load(Ordering::Relaxed) {
            return None;
        }

        unsafe { self.list.remove(data) };
        A::to_links(data).release_after_removal();

        Some(unsafe { A::OwnedType::from_pointer(NonNull::from(data)) })
    }

    /// Removes the element currently at the front of the list and returns it.
    ///
    /// Returns `None` if the list is empty.
    pub fn pop_front(&mut self) -> Option<A::OwnedType> {
        unsafe { self.remove(self.list.front()?.as_ref()) }
    }

    /// Returns an iterator for the list starting at the first entry.
    pub fn iter(&self) -> unsafe_list::Iterator<'_, A> {
        // TODO: Add iterator and Cursor that return the borrowed type rather than the target.
        // This is so that we can get the refcounted objects when the wrapper is Ref<T>.
        self.list.iter()
    }

    /// Returns a cursor starting at the first (front) element of the list.
    pub fn cursor_front(&self) -> Cursor<'_, A> {
        self.list.cursor_front()
    }

    /// Returns a mutable cursor starting at the first (front) element of the list.
    pub fn cursor_front_mut(&mut self) -> CursorMut<'_, A> {
        CursorMut::new_front(self)
    }

    /// Returns a cursor starting at the last (back) element of the list.
    pub fn cursor_back(&self) -> Cursor<'_, A> {
        self.list.cursor_back()
    }

    /// Returns a mutable cursor starting at the last (back) element of the list.
    pub fn cursor_back_mut(&mut self) -> CursorMut<'_, A> {
        CursorMut::new_back(self)
    }
}

impl<A: WrappedAdapter + ?Sized> Default for List<A> {
    fn default() -> Self {
        Self::new()
    }
}

impl<A: WrappedAdapter + ?Sized> Drop for List<A> {
    fn drop(&mut self) {
        while self.pop_front().is_some() {}
    }
}

/// A list cursor that allows traversing a linked list and inspecting & mutating elements.
pub struct CursorMut<'a, A: WrappedAdapter + ?Sized> {
    cursor: unsafe_list::CommonCursor<A>,
    list: &'a mut List<A>,
}

impl<'a, A: WrappedAdapter + ?Sized> CursorMut<'a, A> {
    fn new_front(list: &'a mut List<A>) -> Self {
        let front = list.list.front();
        Self {
            list,
            cursor: unsafe_list::CommonCursor::new(front),
        }
    }

    fn new_back(list: &'a mut List<A>) -> Self {
        let back = list.list.back();
        Self {
            list,
            cursor: unsafe_list::CommonCursor::new(back),
        }
    }

    /// Returns the element the cursor is currently positioned on.
    pub fn current(&mut self) -> Option<&mut <A::OwnedType as TypedPointerWrapper>::Target>
    where
        A::OwnedType: TypedPointerWrapper<Writable = True>,
    {
        let cur = self.cursor.cur?;
        // TODO: Improve justification.
        // SAFETY: Objects must be kept alive while on the list.
        Some(unsafe { &mut *cur.as_ptr() })
    }

    /// Returns a shared (immutable) cursor pointing to the current element.
    pub fn as_cursor(&self) -> Cursor<'_, A> {
        // TODO: Justify.
        unsafe { unsafe_list::Cursor::new(&self.list.list, self.cursor.cur) }
    }

    /// Removes the element the cursor is currently positioned on.
    ///
    /// After removal, it advances the cursor to the next element.
    pub fn remove_current(&mut self) -> Option<A::OwnedType> {
        let entry = self.cursor.cur?;
        self.move_next();
        // SAFETY: The entry is on the list as we just got it from there and it cannot change.
        unsafe { self.list.remove(entry.as_ref()) };
        // SAFETY: Elements on the list were inserted after a call to `into_pointer `.
        Some(unsafe { A::OwnedType::from_pointer(entry) })
    }

    /// Returns the element immediately after the one the cursor is positioned on.
    pub fn peek_next(&mut self) -> Option<&mut <A::OwnedType as TypedPointerWrapper>::Target>
    where
        A::OwnedType: TypedPointerWrapper<Writable = True>,
    {
        let mut new = unsafe_list::CommonCursor::new(self.cursor.cur);
        // SAFETY: `new` was just initialised with a cursor currently in the list, so it is still
        // in the list.
        unsafe { new.move_next(&self.list.list) };
        // TODO: Improve justification below.
        // SAFETY: Objects must be kept alive while on the list.
        Some(unsafe { &mut *new.cur?.as_ptr() })
    }

    /// Returns the element immediately before the one the cursor is positioned on.
    pub fn peek_prev(&mut self) -> Option<&mut <A::OwnedType as TypedPointerWrapper>::Target>
    where
        A::OwnedType: TypedPointerWrapper<Writable = True>,
    {
        let mut new = unsafe_list::CommonCursor::new(self.cursor.cur);
        // SAFETY: `new` was just initialised with a cursor currently in the list, so it is still
        // in the list.
        unsafe { new.move_prev(&self.list.list) };
        // TODO: Improve justification below.
        // SAFETY: Objects must be kept alive while on the list.
        Some(unsafe { &mut *new.cur?.as_ptr() })
    }

    /// Moves the cursor to the next element.
    pub fn move_next(&mut self) {
        // SAFETY: `cursor` starts off in the list and only changes within the list. Additionally,
        // the list cannot change because we hold the only mutable reference to it, so the cursor
        // is always within the list.
        unsafe { self.cursor.move_next(&self.list.list) };
    }

    /// Moves the cursor to the previous element.
    pub fn move_prev(&mut self) {
        // SAFETY: `cursor` starts off in the list and only changes within the list. Additionally,
        // the list cannot change because we hold the only mutable reference to it, so the cursor
        // is always within the list.
        unsafe { self.cursor.move_prev(&self.list.list) };
    }
}
