use ansi_str::AnsiStr;
use owo_colors::{colors::*, OwoColorize};

pub fn main() {
    let text = "When the night has come"
        .fg::<Red>()
        .bg::<Cyan>()
        .bold()
        .to_string();

    let cut = text.ansi_get(5..).expect("ansi_get mustn't fail");

    println!("{text}");
    println!("{cut}");
}
