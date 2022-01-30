use ansi_str::AnsiStr;
use owo_colors::*;

fn main() {
    let s = "Hello".red().on_black().to_string() + " " + &"World".green().on_yellow().to_string();
    let (left, right) = s.ansi_split_at(6);

    println!("text {}", s);
    println!("left {} right {}", left, right);
}
