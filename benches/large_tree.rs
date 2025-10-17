//! This is a pretty unfair benchmark, because we're asking serde_json and saphyr to
//! construct a full in-memory representation but we're not doing that ourselves.
//!
//! This is only because I don't actually know how to ask serde_json to scan the file
//! without constructing a representation.

use std::hint::black_box;

use divan::Bencher;
use json_scanner::{Event, Parser};
use saphyr::LoadableYamlNode;

fn main() {
    divan::main();
}

fn generate_json(depth: usize, branching: usize) -> String {
    fn generate_rec(depth: usize, branching: usize) -> serde_json::Value {
        if depth == 0 {
            serde_json::Value::String("hi".into())
        } else {
            let mut map = serde_json::Map::new();
            for i in 0..branching {
                map.insert(format!("elt_{i}"), generate_rec(depth - 1, branching));
            }
            serde_json::Value::Object(map)
        }
    }
    serde_json::to_string_pretty(&generate_rec(depth, branching)).unwrap()
}

fn scan_json(input: &str) -> Option<Event<'_>> {
    let mut parser = Parser::new(input.as_bytes());
    let mut last_ev = None;
    while let Some(ev) = parser.next_event().unwrap() {
        last_ev = Some(ev.event);
    }
    last_ev
}

#[divan::bench]
fn us(bencher: Bencher) {
    let input = generate_json(6, 10);
    bencher.bench_local(|| black_box(scan_json(&input)));
}

#[divan::bench]
fn serde(bencher: Bencher) {
    let input = generate_json(6, 10);
    bencher.bench_local(|| black_box(serde_json::from_str::<serde_json::Value>(&input).unwrap()));
}

#[divan::bench]
fn saphyr(bencher: Bencher) {
    let input = generate_json(6, 10);
    bencher.bench_local(|| black_box(saphyr::Yaml::load_from_str(&input).unwrap()));
}
