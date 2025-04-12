#![allow(dead_code)]

use std::{env::args, fs::File, io::Read, path::Path};

use anyhow::{Context, Result};

use self::ast::LambdaGame;

mod ast;

fn main() -> Result<()> {
    let path_arg = args().nth(1).context("expected file path")?;
    let mut file = File::open(Path::new(&path_arg)).context("file not found")?;

    let mut program = String::new();
    file.read_to_string(&mut program)
        .context("file read error")?;

    let game = LambdaGame::from(&program);
    println!("{game:?}");

    Ok(())
}
