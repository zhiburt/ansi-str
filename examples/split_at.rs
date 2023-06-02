use ansi_str::AnsiStr;
use owo_colors::*;

fn main() {
    let text = format!(
        "{} {}",
        "Hello".red().on_black(),
        "World".green().on_yellow()
    );

    let (left, right) = text.ansi_split_at(6);

    println!("text {text}");
    println!("left {left}");
    println!("left {right}");
}
