# json-scanner

A minimalist JSON parser that reports positions.

I want to parse JSON, manipulate the results, and then (if necessary) emit
errors that point to locations in the JSON input.
[`toml`](https://crates.io/toml) and [`toml-edit`](https://crates.io/toml_edit)
do this for TOML, so why not JSON?
Well, `serde_json` [doesn't support](https://github.com/serde-rs/json/issues/637)
reporting locations (except on parse errors). [`sonic_rs`](https://docs.rs/sonic-rs/latest/sonic_rs/)
doesn't *seem* to support it either (at least, I couldn't figure out how).
The two best options I could find were [`json-spanned-value`](https://crates.io/crates/json-spanned-value)
and [`json-syntax`](https://crates.io/crates/json-syntax), but they both
require making a trip through a dynamically typed intermediate representation
and I didn't want to do that.

So here's my quick and dirty addition to the zoo of poorly-maintained JSON parsers
on `crates.io`. It's a pull-based streaming JSON parser (delivering events instead
of structured data) that reports positions. That's all it does. Maybe at some
point it can gain a `serde`-ish wrapper like the `toml` crate has with
[`serde_spanned`](https://crates.io/serde_spanned).

```rust
let mut parser = Parser::new(br#"{ "foo": "bar" }"#);
assert_eq!(
  parser.next_event().unwrap().unwrap(),
  SpannedEvent {
    start: 0,
    end: 1,
    event: Event::BeginObject,
  }
);

assert_eq!(
  parser.next_event().unwrap().unwrap(),
  SpannedEvent {
    start: 2,
    end: 7,
    event: Event::String("foo".into()),
  }
);

assert_eq!(
  parser.next_event().unwrap().unwrap(),
  SpannedEvent {
    start: 9,
    end: 14,
    event: Event::String("bar".into()),
  }
);

assert_eq!(
  parser.next_event().unwrap().unwrap(),
  SpannedEvent {
    start: 15,
    end: 16,
    event: Event::EndObject,
  }
);
```

## How does it handle numbers?

It doesn't. It validates them, but leaves them as `&str`. You get to decide how to represent them.

## How does it handle strings?

They must be valid UTF-8, and escaped UTF-16 surrogates must be properly paired. There's no
"tolerant" parsing mode, sorry.

## Does it work?

At least a little. I lifted a bunch of test cases from [`json-syntax`](https://crates.io/crates/json-syntax),
which I believe were mostly lifted from [`JSONTestSuite`](https://github.com/nst/JSONTestSuite).
