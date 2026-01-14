use std::io::stdin;

mod game1 {
    include!("main_halo2_bulletproofs.rs");
}

fn main() {
    println!("Choose the mode for the Battleship game:");
    println!("1. SNARKs (Halo2/Bulletproofs)");

    let mut choice = String::new();
    stdin().read_line(&mut choice).unwrap();

    match choice.trim() {
        "1" => game1::run(),
        _ => {
            println!("Please choose 1.");
            return;
        }
    };
}
