# ansi-str [![Build Status](https://github.com/zhiburt/ansi-str/actions/workflows/ci.yml/badge.svg?style=for-the-badge)](https://github.com/zhiburt/ansi-str/actions) [![codecov](https://codecov.io/gh/zhiburt/ansi-str/branch/master/graph/badge.svg?token=8VGEM3ZT1T)](https://codecov.io/gh/zhiburt/ansi-str) [![Crate](https://img.shields.io/crates/v/ansi-str)](https://crates.io/crates/ansi-str) [![docs.rs](https://img.shields.io/docsrs/ansi_str?color=blue)](https://docs.rs/ansi_cut/0.1.0/ansi_str/)

This is a library for work with coloured and formatted strings on ANSI terminals.

## Usage

```rust
use ansi_str::AnsiStr;
use owo_colors::{colors::*, OwoColorize};

pub fn main() {
    let colored_text = "When the night has come"
        .fg::<Red>()
        .bg::<Cyan>()
        .bold()
        .to_string();

    let s = colored_text.ansi_get(5..).unwrap();

    println!("{}", colored_text);
    println!("{}", s);
}
```

##### [For more examples, you check the directory of the same name.](https://github.com/zhiburt/ansi-str/tree/master/examples).

##### You can find a list of methods which are provided on [the documentation page](https://docs.rs/ansi_cut/*/ansi_str/).

### Note

The library has derivatived from [zhiburt/ansi-cut](https://github.com/zhiburt/ansi-cut)
