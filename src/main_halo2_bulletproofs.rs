// crates: rand, halo2_proofs, pasta_curves,.. and some others I didnt end up using here after testing them out a bit
// the Zordle game was a really good reference for me to understand how to implement a halo2 snarks ZK proof and there's also the halo2 book
// rust install guide... I'm also using rust analyzer on vscode (really good btw.. super responsive and helpful actually)
// https://www.rust-lang.org/tools/install
// some coding references for snarks ZKP in rust using halo2_proofs
// https://github.com/nalinbhardwaj/zordle/blob/main/circuits/src/main.rs
// https://zcash.github.io/halo2/concepts/arithmetization.html
// some coding references for bulletproofs ZKP in rust using using curve25519_dalek, bulletproofs, merlin
// https://github.com/dalek-cryptography/bulletproofs

// cargo.toml contents
// [package]
// name = "zk-battleship"
// version = "0.1.0"
// edition = "2024"

// [dependencies]
// halo2_proofs = "0.3.0"
// rand = "0.8"
// halo2curves = "0.8.0"
// bulletproofs = "5.0.0"
// curve25519-dalek = "4.1.3"
// merlin = "3.0.0"

// dependencies
use std::collections::HashSet;
use std::io::stdin;
use std::fs::File;
use std::io::BufReader;

use rand::Rng;
use rand::rngs::OsRng;
use rand::thread_rng;

use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    plonk::{Circuit, ConstraintSystem, Error, Advice, Instance, Column, Selector, 
        create_proof, verify_proof, keygen_pk, keygen_vk, VerifyingKey, ProvingKey},
    transcript::{Blake2bWrite, Blake2bRead, Challenge255},
    poly::commitment::Params,
    pasta::{Fp, EqAffine},
};

use halo2_proofs::plonk::SingleVerifier;

use bulletproofs::{BulletproofGens, PedersenGens, RangeProof};
use curve25519_dalek::{scalar::Scalar, ristretto::CompressedRistretto};
use merlin::Transcript;

struct BattleshipGame {
    grid_size: usize,
    grid: Vec<Vec<u8>>,
    ship_commitments: HashSet<u64>,
    ship_range_proofs: Vec<ShipPlacementProof>,
    ship_positions: Vec<(u8, u8)>,  // Store actual ship positions
}

#[derive(Clone)]
struct CoordinateProof {
    commitment: CompressedRistretto,
    proof: RangeProof,
}

#[derive(Clone)]
struct ShipPlacementProof {
    x: CoordinateProof,
    y: CoordinateProof,
}

impl BattleshipGame {

    // initializes the game and its start state 
    fn new(size: usize) -> Self {
        BattleshipGame {
            grid_size: size,
            grid: vec![vec![0; size]; size],
            ship_commitments: HashSet::new(),
            ship_range_proofs: Vec::new(),
            ship_positions: Vec::new(),
        }
    }
    // choose number of bits for Bulletproof range: smallest k with 2^k >= grid_size
    // Bulletproofs require bit sizes to be multiples of 8
    fn bits_for_grid_size(&self) -> usize {
        let mut bits = 0usize;
        let mut bound = 1usize;
        while bound < self.grid_size {
            bound <<= 1;
            bits += 1;
        }
        // Round up to nearest multiple of 8
        let bits = bits.max(1);
        ((bits + 7) / 8) * 8
    }

    // Generate and verify a range proof for a coordinate without revealing it
    fn prove_coordinate_range(&self, coord: u8) -> Result<CoordinateProof, String> {
        if coord as usize >= self.grid_size {
            return Err(format!("Coordinate {} out of bounds; must be < {}", coord, self.grid_size));
        }

        let bits = self.bits_for_grid_size();
        let bound = 1u64 << bits;
        if (coord as u64) >= bound {
            return Err(format!(
                "Coordinate {} is not < 2^{} ({}); grid_size={}",
                coord, bits, bound, self.grid_size
            ));
        }

        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(bits, 1);
        let blinding = Scalar::random(&mut thread_rng());
        let mut prover_transcript = Transcript::new(b"battleship_range_proof");

        let (proof, commitment) = RangeProof::prove_single(
            &bp_gens,
            &pc_gens,
            &mut prover_transcript,
            coord as u64,
            &blinding,
            bits,
        ).map_err(|e| format!(
            "Failed to generate range proof (coord={}, bits={}, bound=2^{}={}): {:?}",
            coord, bits, bits, bound, e
        ))?;

        let mut verifier_transcript = Transcript::new(b"battleship_range_proof");
        proof
            .verify_single(
                &bp_gens,
                &pc_gens,
                &mut verifier_transcript,
                &commitment,
                bits,
            )
            .map_err(|_| "Range proof failed".to_string())?;

        Ok(CoordinateProof { commitment, proof })
    }

    // hashes the position of the ship, stores it, and publishes range proofs for coordinates
    fn place_ship(&mut self, x: u8, y: u8) -> Result<(), String> {
        let x_proof = self.prove_coordinate_range(x)?;
        let y_proof = self.prove_coordinate_range(y)?;

        let commitment = Self::hash_position(x, y);
        self.ship_commitments.insert(commitment);
        self.grid[y as usize][x as usize] = 1;
        self.ship_positions.push((x, y));

        self.ship_range_proofs.push(ShipPlacementProof { x: x_proof, y: y_proof });

        println!("Ship placement proof valid");

        Ok(())
    }

    // Verifier-side: check all stored ship placement proofs using current grid-size bits
    fn verify_published_ship_proofs(&self) -> bool {
        let pc_gens = PedersenGens::default();
        let bits = self.bits_for_grid_size();
        let bp_gens = BulletproofGens::new(bits, 1);
        for sp in &self.ship_range_proofs {
            // x
            let mut vt_x = Transcript::new(b"battleship_range_proof");
            if sp.x
                .proof
                .verify_single(&bp_gens, &pc_gens, &mut vt_x, &sp.x.commitment, bits)
                .is_err()
            {
                return false;
            }
            // y
            let mut vt_y = Transcript::new(b"battleship_range_proof");
            if sp.y
                .proof
                .verify_single(&bp_gens, &pc_gens, &mut vt_y, &sp.y.commitment, bits)
                .is_err()
            {
                return false;
            }
        }
        true
    }

    // verifies the attack by checking if the coordinates are in range
    // and if the ship_commitments set contains the hash of the position
    fn verify_attack_range(&mut self, x: u8, y: u8) -> Result<bool, String> {
        self.prove_coordinate_range(x)?;
        self.prove_coordinate_range(y)?;

        let commitment = Self::hash_position(x, y);
        let hit = self.ship_commitments.contains(&commitment);

        Ok(hit)
    }

    // Update grid after SNARK verification
    fn record_hit(&mut self, x: u8, y: u8) {
        self.grid[y as usize][x as usize] = 2;
    }

    // checks if all ships are sunk
    fn all_ships_sunk(&self) -> bool {
        for row in &self.grid {
            for &cell in row {
                if cell == 1 {
                    return false;
                }
            }
        }
        true
    }

    // prints the grid to the console at the end of the game
    fn print_grid(&self) {
        for row in &self.grid {
            for &cell in row {
                if cell == 1 {
                    print!("S "); // Ship
                } else if cell == 2 {
                    print!("X "); // Hit ship
                } else {
                    print!(". "); // Empty
                }
            }
            println!();
        }
    }
    
    // hashes an x and y coordinate to a u64
    fn hash_position(x: u8, y: u8) -> u64 {
        const BASE: u64 = 31;
        let mut hash = 0u64;
        hash += x as u64;
        hash = hash * BASE;
        hash += y as u64;
        hash
    }

}
// Snarks implementation checks if the attack by matching the hashes of the ship and attack positions
#[derive(Clone)]
struct BattleshipCircuit {
    ship_x: Value<Fp>,
    ship_y: Value<Fp>,
    attack_x: Value<Fp>,
    attack_y: Value<Fp>,
    hit: Value<Fp>,
    ship_hash: Value<Fp>,  // The actual ship commitment
}
impl Circuit<Fp> for BattleshipCircuit {
    type Config = (Column<Advice>, Column<Advice>, Column<Advice>, Column<Instance>, Selector);
    type FloorPlanner = SimpleFloorPlanner;

    // no witnesses are needed for the circuit
    fn without_witnesses(&self) -> Self {
        Self {
            ship_x: Value::unknown(),
            ship_y: Value::unknown(),
            attack_x: Value::unknown(),
            attack_y: Value::unknown(),
            hit: Value::unknown(),
            ship_hash: Value::unknown(),
        }
    }

    // configures the circuit
    fn configure(meta: &mut ConstraintSystem<Fp>) -> Self::Config {
        let ship_coords = meta.advice_column();
        let attack_coords = meta.advice_column();
        let result_advice = meta.advice_column();
        let result_instance = meta.instance_column();
        let selector = meta.selector();

        meta.enable_equality(ship_coords);
        meta.enable_equality(attack_coords);
        meta.enable_equality(result_advice);
        meta.enable_equality(result_instance);

        (ship_coords, attack_coords, result_advice, result_instance, selector)
    }


    // synthesizes the circuit
    fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<Fp>) -> Result<(), Error> {
        let (_ship_coords, _attack_coords, result_advice, _result_instance, selector) = config;

        layouter.assign_region(
            || "verify attack",
            |mut region| {
                selector.enable(&mut region, 0)?;

                // Compute the hash of the provided ship position: (x * BASE) + y
                let computed_ship_hash = self.ship_x
                    .clone()
                    .zip(self.ship_y.clone())
                    .map(|(x, y)| (x * Fp::from(31u64)) + y);

                // Verify the provided ship hash matches the committed ship hash
                let ship_hash_cell = region.assign_advice(
                    || "computed ship hash",
                    result_advice,
                    0,
                    || computed_ship_hash
                )?;

                let claimed_ship_hash_cell = region.assign_advice(
                    || "claimed ship hash",
                    result_advice,
                    1,
                    || self.ship_hash
                )?;

                // Constrain that computed ship hash equals claimed ship hash
                region.constrain_equal(ship_hash_cell.cell(), claimed_ship_hash_cell.cell())?;
                // Hash attack position: (x * BASE) + y
                let attack_hash = self.attack_x
                    .clone()
                    .zip(self.attack_y.clone())
                    .map(|(x, y)| (x * Fp::from(31u64)) + y);

                // Compare hashes to determine hit
                let computed_hit = computed_ship_hash.zip(attack_hash)
                    .map(|(s, a)| Fp::from((s == a) as u64));

                // Assign the computed hit
                let hit_check_cell = region.assign_advice(
                    || "hit check",
                    result_advice,
                    2,
                    || computed_hit
                )?;

                // Assign the claimed hit
                let hit_cell = region.assign_advice(
                    || "hit result",
                    result_advice,
                    3,
                    || self.hit
                )?;

                // Constrain that claimed hit matches computed hit
                region.constrain_equal(hit_cell.cell(), hit_check_cell.cell())?;

                // Expose the hit result to public instance (row 0)
                let instance_cell = region.assign_advice(
                    || "expose hit to instance",
                    result_advice,
                    4,
                    || self.hit
                )?;
                region.constrain_equal(hit_cell.cell(), instance_cell.cell())?;

                Ok(())
            },
        )?;

        Ok(())
    }
}

// generates the proof
fn generate_proof(
    params: &Params<EqAffine>,
    pk: &ProvingKey<EqAffine>,
    circuit: BattleshipCircuit,
    public_inputs: &[Fp],
) -> Vec<u8> {
    let mut transcript = Blake2bWrite::<_, EqAffine, Challenge255<EqAffine>>::init(vec![]);
    
    create_proof(
        params,
        pk,
        &[circuit],
        &[&[public_inputs]],
        OsRng,
        &mut transcript,
    )
    .expect("Proof generation should not fail");

    transcript.finalize()
}

// verifies the generated proof
fn verify_proof_strat(
    params: &Params<EqAffine>,
    vk: &VerifyingKey<EqAffine>,
    proof: &[u8],
    public_inputs: &[Fp],
) -> bool {
    
    let strategy = SingleVerifier::new(params);
    let mut transcript = Blake2bRead::<_, EqAffine, Challenge255<_>>::init(proof);

    verify_proof(
        params,
        vk,
        strategy,
        &[&[public_inputs]],
        &mut transcript,
    )
    .is_ok()
}

// num of rows in curcuit which I think is 2^4 = 16 in this case
const K: u32 = 4;

// generates the default params and writes them to a file
fn write_params() {
    let mut params_file = File::create("params.bin").unwrap();
    let params: Params<EqAffine> = Params::new(K);
    params.write(&mut params_file).unwrap();
}

// initializes the params and keys
fn initialize_params() -> (
    Params<EqAffine>,
    ProvingKey<EqAffine>,
    VerifyingKey<EqAffine>
) {
    // file path for params
    let params_path = "params.bin";

    // reads params bin
    let params_file = match File::open(params_path) {
        Ok(file) => file,
        Err(_) => {
            println!("\nParams file not found. Please generate parameters first.");
            println!("Generating parameters now...");
            write_params();
            println!("Parameters generated successfully!\n");
            File::open(params_path).expect("Failed to open newly created params file")
        }
    };

    let params = Params::<EqAffine>::read(&mut BufReader::new(params_file)).expect("Failed to read params");

    let empty_circuit = BattleshipCircuit {
        ship_x: Value::unknown(),
        ship_y: Value::unknown(),
        attack_x: Value::unknown(),
        attack_y: Value::unknown(),
        hit: Value::unknown(),
        ship_hash: Value::unknown(),
    };

    // generates proving and verifying keys
    let vk = keygen_vk(&params, &empty_circuit).expect("Failed to generate verifying key");
    let pk = keygen_pk(&params, vk.clone(), &empty_circuit).expect( "Failed to generate proving key");

    (params, pk, vk)
}

pub fn run() {

    println!("Welcome to Zattleship!");
    
    let input = get_input("Enter 1 to play the game or 2 to generate new parameters");

    if input == 2 {
        write_params();
        println!("Parameters generated successfully!\n");
    }

    // Initialize parameters and keys
    let (params, pk, vk) = initialize_params();

    let grid_size = 10u8;
    let num_ships = get_input("Enter the number of ships: ");

    let mut player_game = BattleshipGame::new(grid_size as usize);
    let mut computer_game = BattleshipGame::new(grid_size as usize);

    // Player ship placement
    println!("\nPlayer placing ships...");
    for _ in 0..num_ships {
        let ship_x = get_input("Enter the ship's x-coordinate: ");
        let ship_y = get_input("Enter the ship's y-coordinate: ");
        if let Err(e) = player_game.place_ship(ship_x, ship_y) {
            println!("Invalid ship placement: {}", e);
            continue;
        }
    }

    // Demonstrate verifier-side check of player's published commitments + proofs
    if player_game.verify_published_ship_proofs() {
        println!("Player ship placement proofs verified against grid bound.");
    } else {
        println!("Player ship placement proof verification FAILED.");
    }

    // Computer ship placement
    println!("\nComputer placing ships...");
    for _ in 0..num_ships {
        let x = rand::thread_rng().gen_range(0..grid_size) as u8;
        let y = rand::thread_rng().gen_range(0..grid_size) as u8;
        
        if computer_game.place_ship(x, y).is_err() {
            // If placement fails, try again
            continue;
        }

       println!("Computer placed ship at ({}, {})", x, y); // for debugging
        
    }

    // Demonstrate verifier-side check of published commitments + proofs
    if computer_game.verify_published_ship_proofs() {
        println!("Computer ship placement proofs verified against grid bound.");
    } else {
        println!("Computer ship placement proof verification FAILED.");
    }

    loop {

        // Player's turn
        // gets player's public inputs

        println!("\nPlayer Attacking");
        let attack_x = get_input("Enter attack x-coordinate: ");
        let attack_y = get_input("Enter attack y-coordinate: ");

        match computer_game.verify_attack_range(attack_x, attack_y) {
            Ok(hit) => {
                if !hit {
                    // For misses, we don't need SNARK verification
                    println!("Attack verified with range proof.");
                    println!("\nMiss!");
                } else {
                    // Only create SNARK proof for hits
                    // Get the actual ship position that was hit
                    let (ship_x_w, ship_y_w) = computer_game.ship_positions.iter()
                        .find(|(x, y)| *x == attack_x && *y == attack_y)
                        .copied()
                        .unwrap_or((attack_x, attack_y));
                    
                    // Get the ship commitment hash for this position
                    let ship_hash = BattleshipGame::hash_position(ship_x_w, ship_y_w);
                    
                    let circuit = BattleshipCircuit {
                        ship_x: Value::known(Fp::from(ship_x_w as u64)),
                        ship_y: Value::known(Fp::from(ship_y_w as u64)),
                        attack_x: Value::known(Fp::from(attack_x as u64)),
                        attack_y: Value::known(Fp::from(attack_y as u64)),
                        hit: Value::known(Fp::from(1u64)),
                        ship_hash: Value::known(Fp::from(ship_hash as u64)),
                    };

                    // Public inputs including hit result
                    let public_inputs = vec![
                        Fp::from(attack_x as u64),
                        Fp::from(attack_y as u64),
                        Fp::from(1u64),
                    ];

                    // generates the proof
                    let proof = generate_proof(&params, &pk, circuit, &public_inputs);

                    // verifies the proof
                    if verify_proof_strat(&params, &vk, &proof, &public_inputs) {
                        println!("Attack verified! with Snarks...");
                        println!("\nHit!");
                        // record the hit on the computer's grid
                        computer_game.record_hit(attack_x, attack_y);
                        
                        // check if all ships are sunk
                        if computer_game.all_ships_sunk() {
                            println!("You win!");
                            break;
                        }
                    } else {
                        println!("Invalid attack! Proof verification failed...");
                    }
                }
            }
            Err(e) => {
                println!("Invalid attack: {}", e);
                continue;
            }
        }

        // computer's turn... this repeats the player process above
        // generates a random attack instead of asking for input
        let attack_x = rand::thread_rng().gen_range(0..grid_size) as u8;
        let attack_y = rand::thread_rng().gen_range(0..grid_size) as u8;

        println!("\nComputer Attacking");
        // println!("Computer's attack: ({}, {})", attack_x, attack_y); // for debugging... gives the player a chance to see the attack like in real battleship

        match player_game.verify_attack_range(attack_x, attack_y) {
            Ok(hit) => {
                if !hit {
                    // For misses, we don't need SNARK verification
                    println!("Attack verified with range proof.");
                    println!("\nMiss!");
                } else {
                    // Only create SNARK proof for hits
                    // Get the actual ship position that was hit
                    let (ship_x_w, ship_y_w) = player_game.ship_positions.iter()
                        .find(|(x, y)| *x == attack_x && *y == attack_y)
                        .copied()
                        .unwrap_or((attack_x, attack_y));
                    
                    // Get the ship commitment hash for this position
                    let ship_hash = BattleshipGame::hash_position(ship_x_w, ship_y_w);
                    
                    let circuit = BattleshipCircuit {
                        ship_x: Value::known(Fp::from(ship_x_w as u64)),
                        ship_y: Value::known(Fp::from(ship_y_w as u64)),
                        attack_x: Value::known(Fp::from(attack_x as u64)),
                        attack_y: Value::known(Fp::from(attack_y as u64)),
                        hit: Value::known(Fp::from(1u64)),
                        ship_hash: Value::known(Fp::from(ship_hash as u64)),
                    };

                    // Public inputs including hit result
                    let public_inputs = vec![
                        Fp::from(attack_x as u64),
                        Fp::from(attack_y as u64),
                        Fp::from(1u64),
                    ];

                    // generates the proof
                    let proof = generate_proof(&params, &pk, circuit, &public_inputs);

                    // verifies the proof
                    if verify_proof_strat(&params, &vk, &proof, &public_inputs) {
                        println!("Attack verified! with Snarks...");
                        println!("\nHit!");
                        // record the hit on the player's grid
                        player_game.record_hit(attack_x, attack_y);
                        
                        // check if all ships are sunk
                        if player_game.all_ships_sunk() {
                            println!("Computer wins!");
                            break;
                        }
                    } else {
                        println!("Invalid attack! Proof verification failed...");
                    }
                }
            }
            Err(e) => {
                println!("Invalid attack: {}", e);
                continue;
            }

        }

    }

    println!("\nPlayers board:");
    player_game.print_grid();
    println!("\nComputer's board:");
    computer_game.print_grid();

}

// couldn't figure out a better way for getting input in rust from terminal
// btw it was picking newlines etc... for while without me noticing and that was really messing with me :(
fn get_input(prompt: &str) -> u8 {
    println!("{}", prompt);
    let mut input = String::new();
    stdin().read_line(&mut input).unwrap();
    input.trim().parse().unwrap() // everthing under the sun to get rid of unwanted inputs fr
}