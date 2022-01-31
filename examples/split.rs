use ansi_str::AnsiStr;
use owo_colors::*;

fn main() {
    let s = "Hello".red().bg_rgb::<23, 11, 100>().to_string()
        + " "
        + &"World".green().on_yellow().to_string();
    let (left, right) = s.ansi_split_at(6);

    println!("text {}", s);
    println!("text {:?}", s);
    println!("left {} right {}", left, right);
    println!("left {:?} right {:?}", left, right);
}
