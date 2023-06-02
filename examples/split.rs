use ansi_str::AnsiStr;
use owo_colors::{colors::*, OwoColorize};

pub fn main() {
    let text = "
        It's funny how life gets complicated
        It's funny how life just takes its toll
        It's funny how everything leads to something
        Now I'm back, where I belong

        X Ambassadors - Belong
    ";

    let colored_text = colorize_text(text);

    for word in colored_text.ansi_split(" ") {
        if word.ansi_strip().trim().is_empty() {
            continue;
        }

        println!("{word}");
    }
}

fn colorize_text(text: &str) -> String {
    let mut buf = Vec::new();
    for line in text.lines() {
        if line.trim().is_empty() {
            continue;
        }

        buf.push(colorize(line));
    }

    buf.join("\n")
}

fn colorize(s: &str) -> String {
    let mut buf = Vec::new();
    for (i, c) in s.chars().enumerate() {
        let s = match i {
            _ if c == ' ' => c.fg::<Black>().to_string(),
            _ if i % 2 == 0 => c.blue().to_string(),
            _ if i % 3 == 0 => c.red().to_string(),
            _ if i % 5 == 0 => c.yellow().to_string(),
            _ => c.cyan().to_string(),
        };

        let s = match i {
            _ if c == ' ' => s.bg::<Black>().to_string(),
            _ if i % 2 == 0 => s.bg::<BrightGreen>().to_string(),
            _ if i % 3 == 0 => s.bg::<BrightBlack>().to_string(),
            _ if i % 5 == 0 => s.bg::<BrightBlue>().to_string(),
            _ => s.bg::<BrightMagenta>().to_string(),
        };

        buf.push(s);
    }

    buf.join("")
}
