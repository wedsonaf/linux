// SPDX-License-Identifier: GPL-2.0

//! Sample kobject implementation.
//!
//! Based on the C example written by Greg Kroah-Hartman <greg@kroah.com>.

#![no_std]
#![feature(allocator_api, global_asm)]

use core::sync::atomic::{AtomicI32, Ordering};
use kernel::{
    c_str, fmt,
    kobject::{self, Attribute, Object},
    parse_i32,
    prelude::*,
};

// This module shows how to create a simple subdirectory in sysfs called
// /sys/kernel/kobject-example. In that directory, 3 files are created:
// "foo", "baz", and "bar". If an integer is written to these files, it can be
// later read out of it.

static FOO: AtomicI32 = AtomicI32::new(0);
static BAZ: AtomicI32 = AtomicI32::new(0);
static BAR: AtomicI32 = AtomicI32::new(0);

// The "foo" file where a static variable is read from and written to.

struct Foo;
impl kobject::ObjectAttributeOps for Foo {
    fn show(_obj: &Object, _attr: &Attribute, out: &mut impl core::fmt::Write) -> Result {
        core::write!(out, "{}\n", FOO.load(Ordering::Relaxed))?;
        Ok(())
    }

    fn store(_obj: &Object, _attr: &Attribute, contents: &[u8]) -> Result<usize> {
        FOO.store(parse_i32(contents, 10)?, Ordering::Relaxed);
        Ok(contents.len())
    }
}

// Sysfs attributes cannot be world-writable.
const FOO_ATTRIBUTE: Attribute = Attribute::<()>::new::<Foo>(c_str!("foo"), 0o644);

// More complex function where we determine which variable is being accessed by
// looking at the attribute for the "baz" and "bar" files.
struct B;
impl kobject::ObjectAttributeOps for B {
    fn show(_obj: &Object, attr: &Attribute, out: &mut impl core::fmt::Write) -> Result {
        let var = if attr.name() == c_str!("baz") {
            &BAZ
        } else {
            &BAR
        };
        core::write!(out, "{}\n", var.load(Ordering::Relaxed))?;
        Ok(())
    }

    fn store(_obj: &Object, attr: &Attribute, contents: &[u8]) -> Result<usize> {
        let var = if attr.name() == c_str!("baz") {
            &BAZ
        } else {
            &BAR
        };
        var.store(parse_i32(contents, 10)?, Ordering::Relaxed);
        Ok(contents.len())
    }
}

const BAZ_ATTRIBUTE: Attribute = Attribute::<()>::new::<B>(c_str!("baz"), 0o644);
const BAR_ATTRIBUTE: Attribute = Attribute::<()>::new::<B>(c_str!("bar"), 0o644);

// Create a group of attributes so that we can create and destroy them all
// at once.
const ATTRS: kobject::Attributes<(), 3> =
    kobject::Attributes::new([&FOO_ATTRIBUTE, &BAZ_ATTRIBUTE, &BAR_ATTRIBUTE]);

// An unnamed attribute group will put all of the attributes directly in
// the kobject directory.  If we specify a name, a subdirectory will be
// created for the attributes with the directory being the name of the
// attribute group.
const ATTR_GROUP: kobject::AttributeGroup = kobject::AttributeGroup::new(None, &ATTRS);

struct Module {
    _kobj: Object,
}

impl KernelModule for Module {
    fn init(_name: &'static CStr, _module: &'static ThisModule) -> Result<Self> {
        // Create a simple kobject with the name of "kobject_example",
        // located under /sys/kernel/
        //
        // As this is a simple directory, no uevent will be sent to
        // userspace.  That is why this function should not be used for
        // any type of dynamic kobjects, where the name and number are
        // not known ahead of time.
        let example_kobj = Object::<()>::try_new_with_parent(
            fmt!("rust_kobject_example"),
            &kobject::kernel(),
            (),
        )?;

        // Create the files associated with this kobject.
        example_kobj.create_group(&ATTR_GROUP)?;

        Ok(Module {
            _kobj: example_kobj,
        })
    }
}

module! {
    type: Module,
    name: b"rust_kobject",
    author: b"Wedson Almeida Filho",
    license: b"GPL v2",
}
