{-# LANGUAGE QuasiQuotes, OverloadedStrings #-}

module Datalog.DataflogTemplate where

import Text.RawString.QQ
import Text.PrettyPrint

import PP

dataflogTemplate :: Doc -> Doc -> Doc -> Doc -> Doc -> Doc -> Doc -> Doc -> Doc -> Doc -> Doc
dataflogTemplate decls facts val relations sets rules delta cleanup undo handlers = [r|#![allow(non_snake_case)]
#![allow(non_camel_case_types)]
#![allow(non_shorthand_field_patterns)]
#![allow(unused_variables)]
#![feature(slice_patterns)]
#![feature(box_patterns)]
#![feature(box_syntax)]
#![feature(match_default_bindings)]
extern crate timely;
extern crate timely_communication;
#[macro_use]
extern crate abomonation;
extern crate differential_dataflow;
extern crate num;

use num::bigint::BigUint;
use abomonation::Abomonation;

#[macro_use] 
extern crate serde_derive;
extern crate serde;
extern crate serde_json;
use std::ops::*;
use serde::ser::*;
use serde::de::*;
use std::str::FromStr;
use serde::de::Error;
use std::collections::HashSet;
use std::collections::HashMap;
use std::iter::FromIterator;
use std::io::{stdin, stdout, Write};
use std::cell::RefCell;
use std::rc::Rc;
use serde_json as json;

use timely::progress::nested::product::Product;
use timely::dataflow::*;
use timely::dataflow::scopes::{Child, Root};
use timely::dataflow::operators::*;
use timely::dataflow::operators::feedback::Handle;
use timely::dataflow::operators::probe::Handle as ProbeHandle;
use timely::progress::timestamp::RootTimestamp;

use timely_communication::Allocator;


use differential_dataflow::input::{Input, InputSession};
use differential_dataflow::{Data, Collection, Hashable};
use differential_dataflow::operators::*;
use differential_dataflow::lattice::Lattice;

/// A collection defined by multiple mutually recursive rules.
///
/// A `Variable` names a collection that may be used in mutually recursive rules. This implementation
/// is like the `Variable` defined in `iterate.rs` optimized for Datalog rules: it supports repeated
/// addition of collections, and a final `distinct` operator applied before connecting the definition.
pub struct Variable<'a, G: Scope, D: Default+Data+Hashable>
where G::Timestamp: Lattice+Ord {
    feedback: Option<Handle<G::Timestamp, u64,(D, Product<G::Timestamp, u64>, isize)>>,
    current: Collection<Child<'a, G, u64>, D>,
    cycle: Collection<Child<'a, G, u64>, D>,
}

impl<'a, G: Scope, D: Default+Data+Hashable> Variable<'a, G, D> where G::Timestamp: Lattice+Ord {
    /// Creates a new `Variable` from a supplied `source` stream.
    pub fn from(source: &Collection<Child<'a, G, u64>, D>) -> Variable<'a, G, D> {
        let (feedback, cycle) = source.inner.scope().loop_variable(u64::max_value(), 1);
        let cycle = Collection::new(cycle);
        let mut result = Variable { feedback: Some(feedback), current: cycle.clone(), cycle: cycle };
        result.add(source);
        result
    }
    /// Adds a new source of data to the `Variable`.
    pub fn add(&mut self, source: &Collection<Child<'a, G, u64>, D>) {
        self.current = self.current.concat(source);
    }
}

impl<'a, G: Scope, D: Default+Data+Hashable> ::std::ops::Deref for Variable<'a, G, D> where G::Timestamp: Lattice+Ord {
    type Target = Collection<Child<'a, G, u64>, D>;
    fn deref(&self) -> &Self::Target {
        &self.cycle
    }
}

impl<'a, G: Scope, D: Default+Data+Hashable> Drop for Variable<'a, G, D> where G::Timestamp: Lattice+Ord {
    fn drop(&mut self) {
        if let Some(feedback) = self.feedback.take() {
            self.current.distinct()
                        .inner
                        .connect_loop(feedback);
        }
    }
}

#[derive(Eq, PartialOrd, PartialEq, Ord, Debug, Clone, Hash)]
struct Uint{x:BigUint}

impl Default for Uint {
    fn default() -> Uint {Uint{x: BigUint::default()}}
}
unsafe_abomonate!(Uint);

impl Serialize for Uint {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where S: Serializer
    {
        serializer.serialize_str(&self.x.to_str_radix(10))
    }
}

impl<'de> Deserialize<'de> for Uint {
    fn deserialize<D>(deserializer: D) -> Result<Uint, D::Error>
        where D: Deserializer<'de>
    {
        match String::deserialize(deserializer) {
            Ok(s) => match BigUint::from_str(&s) {
                        Ok(i)  => Ok(Uint{x:i}),
                        Err(_) => Err(D::Error::custom(format!("invalid integer value: {}", s)))
                     },
            Err(e) => Err(e)
        }
    }
}

impl Uint {
    #[inline]
    pub fn parse_bytes(buf: &[u8], radix: u32) -> Uint {
        Uint{x: BigUint::parse_bytes(buf, radix).unwrap()}
    }
}

impl Shr<usize> for Uint {
    type Output = Uint;

    #[inline]
    fn shr(self, rhs: usize) -> Uint {
        Uint{x: self.x.shr(rhs)}
    }
}

impl Shl<usize> for Uint {
    type Output = Uint;

    #[inline]
    fn shl(self, rhs: usize) -> Uint {
        Uint{x: self.x.shl(rhs)}
    }
}

macro_rules! forward_binop {
    (impl $imp:ident for $res:ty, $method:ident) => {
        impl $imp<$res> for $res {
            type Output = $res;

            #[inline]
            fn $method(self, other: $res) -> $res {
                // forward to val-ref
                Uint{x: $imp::$method(self.x, other.x)}
            }
        }
    }
}

forward_binop!(impl Add for Uint, add);
forward_binop!(impl Sub for Uint, sub);
forward_binop!(impl Div for Uint, div);
forward_binop!(impl Rem for Uint, rem);|]
    $$
    decls
    $$
    facts
    $$
    val
    $$
    relations
    $$ [r|
impl Value {
    fn field(&self) -> &Fact {
        match self {
            &Value::Fact(ref f) => f,
            _ => unreachable!()
        }
    }
}
#[derive(Serialize, Deserialize, Debug)]
enum Request {
    start,
    rollback,
    commit,
    add(Fact),
    del(Fact),
    chk(Relation),
    enm(Relation)
}

#[derive(Serialize, Deserialize, Debug)]
enum Response<T> {
    err(String),
    ok(T)
}

fn xupd(s: &Rc<RefCell<HashSet<Value>>>, ds: &Rc<RefCell<HashMap<Value, i8>>>, x : &Value, w: isize) 
{
    if w > 0 {
        let new = s.borrow_mut().insert(x.clone());
        if new {
            let f = |e: &mut i8| if *e == -1 {*e = 0;} else if *e == 0 {*e = 1};
            f(ds.borrow_mut().entry(x.clone()).or_insert(0));
        };
    } else if w < 0 {
        let present = s.borrow_mut().remove(x);
        if present {
            let f = |e: &mut i8| if *e == 1 {*e = 0;} else if *e == 0 {*e = -1;};
            f(ds.borrow_mut().entry(x.clone()).or_insert(0));
        };
    }
}

fn upd(s: &Rc<RefCell<HashSet<Value>>>, x: &Value, w: isize) 
{
    if w > 0 {
        s.borrow_mut().insert(x.clone());
    } else if w < 0 {
        s.borrow_mut().remove(x);
    }
}

fn main() {

    // start up timely computation
    timely::execute_from_args(std::env::args(), |worker| {
        let probe = probe::Handle::new();
        let mut probe1 = probe.clone();

        let mut xaction : bool = false;|]
    $$
    (nest' $ nest' sets)
    $$
    (nest' $ nest' rules)
    $$ [r|        
        let mut epoch = 0;
        let mut need_to_flush = false;
        let stream = json::Deserializer::from_reader(stdin()).into_iter::<Request>();

        for val in stream {
            //print!("epoch: {}\n", epoch);
            let req = match val {
                            Ok(r)  => {
                                //print!("r: {:?}\n", r);
                                r
                            },
                            Err(e) => {
                                print!("{}\n", e);
                                std::process::exit(-1);
                            }
                        };

            fn advance(rels : &mut [InputSession<u64, Value, isize>], epoch : u64) {
                for r in rels.into_iter() {
                    //print!("advance\n");
                    r.advance_to(epoch);
                };
            }

            fn flush( rels : &mut [InputSession<u64, Value, isize>]
                    , probe : &ProbeHandle<Product<RootTimestamp, u64>>
                    , worker : &mut Root<Allocator>
                    , need_to_flush : &mut bool) {
                if *need_to_flush {
                    for r in rels.into_iter() {
                        //print!("flush\n");
                        r.flush();
                    };
                    while probe.less_than(rels[0].time()) {
                        worker.step();
                    };
                    *need_to_flush = false
                }
            }

           
            fn insert( rels : &mut [InputSession<u64, Value, isize>], 
                      epoch : &mut u64, 
                      rel : usize, 
                      set : &Rc<RefCell<HashSet<Value>>>, 
                      v: &Value,
                      need_to_flush: &mut bool)
            {
                if !set.borrow().contains(&v) {
                    //print!("new value: {:?}\n", v);
                    rels[rel].insert(v.clone());
                    
                    *epoch = *epoch+1;
                    //print!("epoch: {}\n", epoch);
                    advance(rels, *epoch);
                    *need_to_flush = true
                };
            }

            fn insert_resp (rels : &mut [InputSession<u64, Value, isize>], 
                            epoch : &mut u64, 
                            rel : usize, 
                            set : &Rc<RefCell<HashSet<Value>>>, 
                            v: &Value,
                            need_to_flush : &mut bool)
            {
                insert(rels, epoch, rel, set, v, need_to_flush);
                let resp: Response<()> = Response::ok(());
                serde_json::to_writer(stdout(), &resp).unwrap();
                stdout().flush().unwrap();
            }

            fn remove (rels : &mut [InputSession<u64, Value, isize>], 
                       epoch : &mut u64, 
                       rel : usize, 
                       set : &Rc<RefCell<HashSet<Value>>>, 
                       v: &Value,
                       need_to_flush : &mut bool) 
            {
                if set.borrow().contains(&v) {
                    rels[rel].remove(v.clone());
                    *epoch = *epoch+1;
                    advance(rels, *epoch);
                    *need_to_flush = true
                };
            }

            fn remove_resp (rels : &mut [InputSession<u64, Value, isize>], 
                            epoch : &mut u64, 
                            rel : usize, 
                            set : &Rc<RefCell<HashSet<Value>>>, 
                            v: &Value,
                            need_to_flush : &mut bool) 
            {
                remove(rels, epoch, rel, set, v, need_to_flush);
                let resp: Response<()> = Response::ok(());
                serde_json::to_writer(stdout(), &resp).unwrap();
                stdout().flush().unwrap();
            }

            fn check ( rels : &mut [InputSession<u64, Value, isize>]
                     , probe : &ProbeHandle<Product<RootTimestamp, u64>>
                     , worker : &mut Root<Allocator>
                     , need_to_flush : &mut bool
                     , set : &Rc<RefCell<HashSet<Value>>>) 
            {
                flush(rels, probe, worker, need_to_flush);
                let resp = Response::ok(!set.borrow().is_empty());
                serde_json::to_writer(stdout(), &resp).unwrap();
                stdout().flush().unwrap();
            }

            fn enm ( rels : &mut [InputSession<u64, Value, isize>]
                   , probe : &ProbeHandle<Product<RootTimestamp, u64>>
                   , worker : &mut Root<Allocator>
                   , need_to_flush : &mut bool
                   , set : &Rc<RefCell<HashSet<Value>>>)
            {
                flush(rels, probe, worker, need_to_flush);
                let resp = Response::ok(Vec::from_iter((**set).borrow().iter().map(|x| match x {&Value::Fact(ref f) => f.clone(), _ => unreachable!()})));
                serde_json::to_writer(stdout(), &resp).unwrap();
                stdout().flush().unwrap();
            }|]
    $$
    (nest' $ nest' $ nest' delta)
    $$ 
    (nest' $ nest' $ nest' cleanup)
    $$
    (nest' $ nest' $ nest' undo)
    $$ [r|
            match req {
                Request::start                       => {
                    flush(&mut rels, &probe, worker, &mut need_to_flush);
                    let resp = if xaction {
                                   Response::err(format!("transaction already in progress"))
                               } else {
                                   delta_cleanup!();
                                   xaction = true;
                                   Response::ok(())
                               };
                    serde_json::to_writer(stdout(), &resp).unwrap();
                    stdout().flush().unwrap();
                },
                Request::rollback                    => {
                    flush(&mut rels, &probe, worker, &mut need_to_flush);
                    let resp = if !xaction {
                                   Response::err(format!("no transaction in progress"))
                               } else {
                                   delta_undo!();
                                   delta_cleanup!();
                                   xaction = false;
                                   Response::ok(())
                               };
                    serde_json::to_writer(stdout(), &resp).unwrap();
                    stdout().flush().unwrap();
                },
                Request::commit                      => {
                    flush(&mut rels, &probe, worker, &mut need_to_flush);
                    let resp = if !xaction {
                                   Response::err(format!("no transaction in progress"))
                               } else {
                                   let mut delta = HashSet::new();
                                   delta!(delta);
                                   delta_cleanup!();
                                   xaction = false;
                                   Response::ok(delta)
                              };
                    serde_json::to_writer(stdout(), &resp).unwrap();
                    stdout().flush().unwrap();
                },|]
    $$
    (nest' $ nest' $ nest' $ nest' handlers)
{-    $$ [r|
                    _ => {
                        let resp: Response<()> = Response::err(format!("unknown request: {:?}", req));
                        serde_json::to_writer(stdout(), &resp).unwrap();
                    }
                };-}
    $$ [r|
            };
        };
    }).unwrap();
}|]

cargoTemplate :: String -> Doc
cargoTemplate specname  = [r|[package]
name = "|]
    <> pp specname <> [r|"
version = "0.1.0"

[dependencies.graph_map]
git="https://github.com/frankmcsherry/graph-map.git"

[dependencies.differential-dataflow]
git="https://github.com/frankmcsherry/differential-dataflow.git"

[dependencies.timely]
git="https://github.com/frankmcsherry/timely-dataflow.git"

[dependencies.timely_communication]
git = "https://github.com/frankmcsherry/timely-dataflow"

[dependencies.abomonation]
git="https://github.com/frankmcsherry/abomonation.git"

[dev-dependencies]
getopts="0.2.14"
rand="0.3.13"
byteorder="0.4.2"
itertools="^0.6"

[dependencies]
fnv="1.0.2"
num = "0.1.40"
serde = "1.0.14"
serde_derive = "1.0.14"
serde_json = "1.0.3"

[features]
default = []
logging = ["timely/logging"]

[profile.release]
opt-level = 1
debug = false
rpath = false
lto = false
debug-assertions = false

[[bin]]
name = "|] <> pp specname <> [r|"
path = "./|] <> pp specname <> [r|.rs"|]
