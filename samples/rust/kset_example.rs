// SPDX-License-Identifier: GPL-2.0

//! Sample kset and ktype implementation.
//!
//! Based on the C example written by Greg Kroah-Hartman <greg@kroah.com>.

#![no_std]
#![feature(allocator_api, global_asm)]

use core::sync::atomic::{AtomicI32, Ordering};
use kernel::{
    c_str, fmt,
    kobject::{self, Attribute, Object, Set},
    parse_i32,
    prelude::*,
};

// This module shows how to create a kset in sysfs called
// /sys/kernel/kset-example
// Then three kobjects are created and assigned to this kset, "foo", "baz",
// and "bar". In those kobjects, attributes of the same name are also
// created and if an integer is written to these files, it can be later
// read out of it.

// This is our "object" that we will create a few of and register them with
// sysfs.
struct Foo {
    foo: AtomicI32,
    baz: AtomicI32,
    bar: AtomicI32,
}

// a custom attribute that works just for a struct foo_obj.
struct FooAttributeInfo {
    show: Option<fn(&Object<Foo>, &Attribute<Foo>, &mut dyn core::fmt::Write) -> Result>,
    store: Option<fn(&Object<Foo>, &Attribute<Foo>, &[u8]) -> Result<usize>>,
}

impl kobject::Type for Foo {
    type AttributeExtraInfo = FooAttributeInfo;

    const ATTRIBUTE_GROUPS: kobject::AttributeGroupsUnsized<'static, Self> = ATTR_GROUPS.groups();

    fn show(obj: &Object<Foo>, attr: &Attribute<Foo>, out: &mut impl core::fmt::Write) -> Result {
        if let Some(cb) = &attr.show {
            cb(obj, attr, out)
        } else {
            Err(Error::EIO)
        }
    }

    fn store(obj: &Object<Foo>, attr: &Attribute<Foo>, contents: &[u8]) -> Result<usize> {
        if let Some(cb) = &attr.store {
            cb(obj, attr, contents)
        } else {
            Err(Error::EIO)
        }
    }
}

fn foo_show(obj: &Object<Foo>, _attr: &Attribute<Foo>, out: &mut dyn core::fmt::Write) -> Result {
    core::write!(out, "{}\n", obj.foo.load(Ordering::Relaxed))?;
    Ok(())
}

fn foo_store(obj: &Object<Foo>, _attr: &Attribute<Foo>, contents: &[u8]) -> Result<usize> {
    obj.foo.store(parse_i32(contents, 10)?, Ordering::Relaxed);
    Ok(contents.len())
}

// Sysfs attributes cannot be world-writable.
const FOO_ATTRIBUTE: Attribute<Foo> = Attribute::<Foo>::new(
    c_str!("foo"),
    0o644,
    FooAttributeInfo {
        show: Some(foo_show),
        store: Some(foo_store),
    },
);

// More complex function where we determine which variable is being accessed by
// looking at the attribute for the "baz" and "bar" files.
fn b_show(obj: &Object<Foo>, attr: &Attribute<Foo>, out: &mut dyn core::fmt::Write) -> Result {
    let var = if attr.name() == c_str!("baz") {
        &obj.baz
    } else {
        &obj.bar
    };
    core::write!(out, "{}\n", var.load(Ordering::Relaxed))?;
    Ok(())
}

fn b_store(obj: &Object<Foo>, attr: &Attribute<Foo>, contents: &[u8]) -> Result<usize> {
    let var = if attr.name() == c_str!("baz") {
        &obj.baz
    } else {
        &obj.bar
    };
    var.store(parse_i32(contents, 10)?, Ordering::Relaxed);
    Ok(contents.len())
}

const BAZ_ATTRIBUTE: Attribute<Foo> = Attribute::<Foo>::new(
    c_str!("baz"),
    0o644,
    FooAttributeInfo {
        show: Some(b_show),
        store: Some(b_store),
    },
);
const BAR_ATTRIBUTE: Attribute<Foo> = Attribute::<Foo>::new(
    c_str!("bar"),
    0o644,
    FooAttributeInfo {
        show: Some(b_show),
        store: Some(b_store),
    },
);

const ATTRS: kobject::Attributes<Foo, 3> =
    kobject::Attributes::new([&FOO_ATTRIBUTE, &BAZ_ATTRIBUTE, &BAR_ATTRIBUTE]);

const ATTR_GROUP: kobject::AttributeGroup<Foo> = kobject::AttributeGroup::new(None, &ATTRS);

const ATTR_GROUPS: kobject::AttributeGroups<Foo, 1> = kobject::AttributeGroups::new([&ATTR_GROUP]);

struct Module {
    _foo: Object<Foo>,
    _baz: Object<Foo>,
    _bar: Object<Foo>,
    _set: Set,
}

fn create_foo_obj(name: core::fmt::Arguments<'_>, kset: &Set) -> Result<Object<Foo>> {
    let foo = kset.try_new_object::<Foo>(
        name,
        Foo {
            foo: AtomicI32::new(0),
            baz: AtomicI32::new(0),
            bar: AtomicI32::new(0),
        },
    )?;
    foo.uevent(kobject::Action::Add)?;
    Ok(foo)
}

impl KernelModule for Module {
    fn init(_name: &'static CStr, _module: &'static ThisModule) -> Result<Self> {
        let set = Set::try_new(c_str!("rust_kset_example"), Some(&kobject::kernel()))?;

        let foo = create_foo_obj(fmt!("foo"), &set)?;
        let bar = create_foo_obj(fmt!("bar"), &set)?;
        let baz = create_foo_obj(fmt!("baz"), &set)?;
        Ok(Module {
            _set: set,
            _foo: foo,
            _bar: bar,
            _baz: baz,
        })
    }
}

module! {
    type: Module,
    name: b"rust_kset",
    author: b"Wedson Almeida Filho",
    license: b"GPL v2",
}
