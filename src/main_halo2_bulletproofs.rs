// crates: rand, halo2_proofs, pasta_curves,.. and some others I didnt end up using here after testing them out a bit
// the Zordle game was a really good reference for me to understand how to implement a halo2 snarks ZK proof and there's also the halo2 book
// rust install guide... I'm also using rust analyzer on vscode (really good btw.. super responsive and helpful actually)
    // https://www.rust-lang.org/tools/install
    // https://www.scs.stanford.edu/~zyedidia/docs/rust/rust_book.pdf
    // https://zcash.github.io/halo2/index.html
// some coding references for snarks ZKP in rust using halo2_proofs
    // https://github.com/nalinbhardwaj/zordle/blob/main/circuits/src/main.rs
    // https://zcash.github.io/halo2/concepts/arithmetization.html
// some coding references for bulletproofs ZKP in rust using using curve25519_dalek, bulletproofs, merlin
    // https://github.com/dalek-cryptography/bulletproofs

// additional references since readjusting the code
// Poseiden hashing documentation 
    // https://docs.rs/halo2_gadgets/latest/halo2_gadgets/#chips
    // https://docs.rs/halo2_gadgets/latest/halo2_gadgets/poseidon/index.html

// cargo.toml contents
// [package]
// name = "zk-battleship"
// version = "0.1.0"
// edition = "2024"

// [dependencies]
// halo2_proofs = "0.3.0"
// halo2_gadgets = "0.3.0"
// rand = "0.8"
// halo2curves = "0.8.0"
// bulletproofs = "5.0.0"
// curve25519-dalek = "4.1.3"
// merlin = "3.0.0"

// dependencies
use std::io::stdin;
use std::fs::File;
use std::io::BufReader;

use rand::Rng;
use rand::rngs::OsRng;
use rand::RngCore;

use halo2_gadgets::poseidon::{
    primitives::{ConstantLength, P128Pow5T3, Hash as PoseidonPrimitiveHash},
    Pow5Chip, Pow5Config,
};

use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    plonk::{Circuit, ConstraintSystem, Error, Advice, Instance, Column, Selector,
        create_proof, verify_proof, keygen_pk, keygen_vk, VerifyingKey, ProvingKey},
    poly::commitment::Params,
    transcript::{Blake2bWrite, Blake2bRead, Challenge255},
    pasta::{Fp, EqAffine},
};

use halo2_proofs::plonk::SingleVerifier;

use bulletproofs::{BulletproofGens, PedersenGens, RangeProof};
use curve25519_dalek::{scalar::Scalar, ristretto::CompressedRistretto};
use merlin::Transcript;

#[derive(Clone, Debug)]
struct ShipCommitment {
    commitment:  Fp,    
    salt: u64,          // random salt for blinding
}

struct BattleshipGame {
    grid_size: usize,
    grid: Vec<Vec<u8>>,
    ship_commitments: Vec<ShipCommitment>,
    ship_positions: Vec<(u8, u8)>,
    ship_range_proofs: Vec<ShipPlacementProof>,
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
            grid_size: size, // e.g., 10 for a 10x10 grid
            grid: vec![vec![0; size]; size], // 0: empty, 1: ship, 2: hit
            ship_commitments: Vec::new(),   // stores commitments for ship positions
            ship_positions: Vec::new(),     // stores ship (x, y) coordinates
            ship_range_proofs: Vec::new(), // stores range proofs for ship placements
        }
    }

    // number of ships still afloat
    fn ships_remaining(&self) -> usize {
        self.grid
            .iter()
            .map(|row| row.iter().filter(|&&cell| cell == 1).count())
            .sum()
    }

    // user facing debug output for commitments
    fn print_commitments(&self, label: &str) {
        println!("\n{} commitments (Poseidon digests):", label);
        if self.ship_commitments.is_empty() {
            println!("- none committed yet");
            return;
        }
        for (idx, ShipCommitment { commitment, .. }) in self.ship_commitments.iter().enumerate() {
            println!("- #{} => {:?}", idx + 1, commitment);
        }
        println!("(hashes are public; salts stay hidden to preserve secrecy)\n");
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
        let blinding = Scalar::random(&mut OsRng);
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

    // Creates cryptographic commitment for ship position and stores it with range proofs
    fn place_ship(&mut self, x: u8, y: u8) -> Result<(), String> {
        let x_proof = self.prove_coordinate_range(x)?;
        let y_proof = self.prove_coordinate_range(y)?;

        let commitment = Self::commit_position(x, y);
        self.ship_commitments.push(commitment);        
        self.ship_positions.push((x, y));
        self.grid[y as usize][x as usize] = 1;

        self.ship_range_proofs.push(ShipPlacementProof { x: x_proof, y: y_proof });

        println!("Ship placement proof valid");

        Ok(())
    }

    // check all stored ship placement proofs using current grid-size bits
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
    // and if any ship commitment matches this position
    fn verify_attack_range(&mut self, x: u8, y: u8) -> Result<bool, String> {
        self.prove_coordinate_range(x)?;
        self.prove_coordinate_range(y)?;

        // Check if any stored commitment matches this position
        let hit = self.ship_commitments.iter().any(|commitment| {
            Self::verify_commitment(x, y, commitment.salt, commitment.commitment)
        });

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
    
    // Creates a cryptographically secure commitment to a position using Poseidon hash with random salt
    fn commit_position(x: u8, y: u8) -> ShipCommitment {
        let salt = OsRng.next_u64();
    
        let message = [
            Fp::from(x as u64),
            Fp::from(y as u64),
            Fp::from(salt),
        ];
        
        let commitment = PoseidonPrimitiveHash::<Fp, P128Pow5T3, ConstantLength<3>, 3, 2>::init()
            .hash(message);
        
        ShipCommitment {commitment, salt}
    }

    // Computes Poseidon hash of position with salt
    fn compute_commitment(x: u8, y: u8, salt: u64) -> Fp {
        let message = [
            Fp::from(x as u64),
            Fp::from(y as u64),
            Fp::from(salt),
        ];
    
        PoseidonPrimitiveHash::<Fp, P128Pow5T3, ConstantLength<3>, 3, 2>::init()
            .hash(message)
    }

    // Verifies that a position matches a commitment
    fn verify_commitment(x: u8, y: u8, salt: u64, commitment: Fp) -> bool {
        let computed = Self::compute_commitment(x, y, salt);
        computed == commitment
    }

}
// SNARK circuit verifies that attack coordinates match ship coordinates
#[derive(Clone)]
struct BattleshipCircuit {
    ships: Vec<(Value<Fp>, Value<Fp>, Value<Fp>)>, // (x, y, salt) for each ship           
    published_commitments: Vec<Value<Fp>>, // commitments for each ship
    attack_x: Value<Fp>, // attack x-coordinate
    attack_y: Value<Fp>, // attack y-coordinate
    hit: Value<Fp>,      // 1 if hit, 0 if miss
}

impl Circuit<Fp> for BattleshipCircuit {
    type Config = (Pow5Config<Fp, 3, 2>, Column<Advice>, Column<Advice>, Column<Instance>, Selector);
    type FloorPlanner = SimpleFloorPlanner;

    // no witnesses are needed for the circuit
    fn without_witnesses(&self) -> Self {
        Self {
            ships: Vec::new(),
            published_commitments: Vec::new(),
            attack_x: Value::unknown(),
            attack_y: Value::unknown(),
            hit: Value::unknown(),
        }
    }

    // configures the circuit with proper constraint gates for hit verification
    fn configure(meta: &mut ConstraintSystem<Fp>) -> Self::Config {

        let state = [
            meta.advice_column(),
            meta.advice_column(),
            meta.advice_column(),
        ];

        let partial_sbox = meta.advice_column();
        
        let rc_a = [
            meta.fixed_column(),
            meta.fixed_column(),
            meta.fixed_column(),
        ];

        let rc_b = [
            meta.fixed_column(),
            meta.fixed_column(),
            meta.fixed_column(),
        ];
        
        meta.enable_constant(rc_b[0]);
        
        let poseidon_config = Pow5Chip::configure::<P128Pow5T3>(
            meta,
            state,
            partial_sbox,
            rc_a,
            rc_b,
        );

        let advice = meta.advice_column();
        let result = meta.advice_column();
        let instance = meta.instance_column();
        let selector = meta.selector();

        // enables equality constraints on columns that will use constrain_equal or else Halo2 will panic
        meta.enable_equality(advice);
        meta.enable_equality(result);
        meta.enable_equality(instance);

        (poseidon_config, advice, result, instance, selector)
    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<Fp>) -> Result<(), Error> {

        let (poseidon_config, advice_col, result_col, instance_col, selector) = config;

        // verify each ship's commitment

         for (i, (ship, published_commitment)) in self.ships.iter()
            .zip(self.published_commitments.iter())
            .enumerate()
        {
            let (ship_x, ship_y, salt) = ship;
            
            // assign ship values to cells first or else poseidon hashing won't work (i think its because of how halo2 works with layouters and regions)
            let message: [halo2_proofs::circuit::AssignedCell<Fp, Fp>; 3] = layouter.assign_region(
                || format!("assign_ship_values_{}", i),
                |mut region| {
                    let x_cell = region.assign_advice(
                        || "ship_x",
                        advice_col,
                        0,
                        || *ship_x,
                    )?;
                    let y_cell = region.assign_advice(
                        || "ship_y",
                        advice_col,
                        1,
                        || *ship_y,
                    )?;
                    let salt_cell = region.assign_advice(
                        || "salt",
                        advice_col,
                        2,
                        || *salt,
                    )?;
                    Ok([x_cell, y_cell, salt_cell])
                },
            )?;
            
            // Create Poseidon hasher for this ship
            let poseidon_chip = Pow5Chip::construct(poseidon_config.clone());
            let hasher = halo2_gadgets::poseidon::Hash::<Fp, Pow5Chip<Fp, 3, 2>, P128Pow5T3, halo2_gadgets::poseidon::primitives::ConstantLength<3>, 3, 2>::init(
                poseidon_chip,
                layouter.namespace(|| format!("poseidon_init_{}", i)),
            )?;
            
            // Hash ship data hash(x, y, salt)
            let computed_commitment = hasher.hash(
                layouter.namespace(|| format!("hash_ship_{}", i)),
                message,
            )?;

            // Verify computed commitment == published commitment
            layouter.assign_region(
                || format!("verify_commitment_{}", i),
                |mut region| {
                    let published = region.assign_advice(
                        || "published_commitment",
                        advice_col,
                        0,
                        || *published_commitment,
                    )?;
                    
                    // Constrain equality
                    region.constrain_equal(computed_commitment.cell(), published.cell())?;
                    
                    Ok(())
                },
            )?;
        }

        // Computes whether any ship matches attack

        let mut computed_hit = Value::known(Fp::zero());
        
        for (ship_x, ship_y, _salt) in &self.ships {
            // Checks if ship[i] matches the attack coordinates
            let this_ship_matches = ship_x.zip(self.attack_x)
                .zip(ship_y.zip(self.attack_y))
                .map(|((sx, ax), (sy, ay))| {
                    let x_eq = if sx == ax { Fp::one() } else { Fp::zero() };
                    let y_eq = if sy == ay { Fp::one() } else { Fp::zero() };
                    x_eq * y_eq  // AND logic both must be 1
                });
            
            // computed_hit = computed_hit OR this_ship_matches
            // boolean OR which is a + b - a*b
            computed_hit = computed_hit.zip(this_ship_matches)
                .map(|(acc, matches)| {
                    acc + matches - (acc * matches)
                });
        }

        // Verify hit and expose to instance column in single region
        let hit_cell = layouter.assign_region(
            || "verify_and_expose_hit",
            |mut region| {
                selector.enable(&mut region, 0)?;

                // assigns computed hit value (from circuit logic)
                let computed_cell = region.assign_advice(
                    || "computed_hit",
                    result_col,
                    0,
                    || computed_hit,
                )?;

                // assigns claimed hit value (public input)
                let claimed_cell = region.assign_advice(
                    || "claimed_hit",
                    result_col,
                    1,
                    || self.hit,
                )?;

                // contraint for proof computed must equal claimed
                region.constrain_equal(computed_cell.cell(), claimed_cell.cell())?;

                Ok(computed_cell)
            },
        )?;
        
        layouter.constrain_instance(hit_cell.cell(), instance_col, 0)?;

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

// num of rows in curcuit which I think is 2^8 = 256 in this case (added more for poseidon hashing)
const K: u32 = 8;

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
        ships: Vec::new(),
        published_commitments: Vec::new(),
        attack_x: Value::unknown(),
        attack_y: Value::unknown(),
        hit: Value::unknown(),
    };

    // generates proving and verifying keys
    let vk = keygen_vk(&params, &empty_circuit).expect("Failed to generate verifying key");
    let pk = keygen_pk(&params, vk.clone(), &empty_circuit).expect( "Failed to generate proving key");

    (params, pk, vk)
}

pub fn run() {

    println!("Welcome to Zattleship!");
    
    let input = get_input("Enter 1 to play the game or 2 to generate new parameters");

    let verbose_mode = get_bool("Enable verbose game output? (1=yes, 0=no): ");
    let view_opponent_hashes = get_bool(
        "View opponent's committed hashes after setup? (1=yes, 0=no): ",
    );

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
        if verbose_mode {
            println!("Player committed ship at ({}, {})", ship_x, ship_y);
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

        println!("Computer's ship at: ({}, {})", x, y); // for debugging... reveals computer ship positions
        
        if computer_game.place_ship(x, y).is_err() {
            // if placement fails try again
            continue;
        }

        if verbose_mode {
            println!("Computer committed ship at ({}, {})", x, y);
        }
        
    }

    // Demonstrate verifier-side check of published commitments + proofs
    if computer_game.verify_published_ship_proofs() {
        println!("Computer ship placement proofs verified against grid bound.");
    } else {
        println!("Computer ship placement proof verification FAILED.");
    }

    if view_opponent_hashes {
        computer_game.print_commitments("Computer");
        player_game.print_commitments("Player");
    }

    loop {

        if verbose_mode {
            println!(
                "Status — your ships left: {}, computer ships left: {}",
                player_game.ships_remaining(),
                computer_game.ships_remaining()
            );
        }

        // Player's turn
        // gets player's public inputs

        println!("\nPlayer Attacking");
        let attack_x = get_input("Enter attack x-coordinate: ");
        let attack_y = get_input("Enter attack y-coordinate: ");

        match computer_game.verify_attack_range(attack_x, attack_y) {
            Ok(hit) => {
                // For both hits and misses, create SNARK proof to verify validity
                // Get all ship commitments available to the circuit
                let mut ships = Vec::new();
                let mut commitments = Vec::new();
                
                for (i, ship_commitment) in computer_game.ship_commitments.iter().enumerate() {
                    let (ship_x, ship_y) = computer_game.ship_positions[i];
                    ships.push((
                        Value::known(Fp::from(ship_x as u64)),
                        Value::known(Fp::from(ship_y as u64)),
                        Value::known(Fp::from(ship_commitment.salt)),
                    ));
                    commitments.push(Value::known(ship_commitment.commitment));
                }

                let commitments_count = commitments.len();
                let circuit = BattleshipCircuit {
                    ships,
                    published_commitments: commitments,
                    attack_x: Value::known(Fp::from(attack_x as u64)),
                    attack_y: Value::known(Fp::from(attack_y as u64)),
                    hit: Value::known(Fp::from(if hit { 1u64 } else { 0u64 })),
                };

                // Public inputs including hit/miss result
                let public_inputs = vec![
                    Fp::from(if hit { 1u64 } else { 0u64 }),
                ];

                // generates the proof
                let proof = generate_proof(&params, &pk, circuit, &public_inputs);

                // verifies the proof
                if verify_proof_strat(&params, &vk, &proof, &public_inputs) {
                    println!("Attack verified with SNARKs!");
                    if verbose_mode {
                        println!("Player attack commitments count: {}", commitments_count);
                    }
                    if hit {
                        println!("\nHit!");
                        // record the hit on the computer's grid
                        computer_game.record_hit(attack_x, attack_y);
                        
                        // check if all ships are sunk
                        if computer_game.all_ships_sunk() {
                            println!("You win!");
                            break;
                        }
                    } else {
                        println!("\nMiss!");
                    }
                } else {
                    println!("Invalid attack! Proof verification failed...");
                    if verbose_mode {
                        println!("Proof validation failed for player attack ({}, {})", attack_x, attack_y);
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
                // For both hits and misses, create SNARK proof to verify validity
                // Get all ship commitments available to the circuit
                let mut ships = Vec::new();
                let mut commitments = Vec::new();
                
                for (i, ship_commitment) in player_game.ship_commitments.iter().enumerate() {
                    let (ship_x, ship_y) = player_game.ship_positions[i];
                    ships.push((
                        Value::known(Fp::from(ship_x as u64)),
                        Value::known(Fp::from(ship_y as u64)),
                        Value::known(Fp::from(ship_commitment.salt)),
                    ));
                    commitments.push(Value::known(ship_commitment.commitment));
                }

                let commitments_count = commitments.len();
                let circuit = BattleshipCircuit {
                    ships,
                    published_commitments: commitments,
                    attack_x: Value::known(Fp::from(attack_x as u64)),
                    attack_y: Value::known(Fp::from(attack_y as u64)),
                    hit: Value::known(Fp::from(if hit { 1u64 } else { 0u64 })),
                };

                // Public inputs including hit/miss result
                let public_inputs = vec![
                    Fp::from(if hit { 1u64 } else { 0u64 }),
                ];

                // generates the proof
                let proof = generate_proof(&params, &pk, circuit, &public_inputs);

                // verifies the proof
                if verify_proof_strat(&params, &vk, &proof, &public_inputs) {
                    println!("Attack verified with SNARKs!");
                    if verbose_mode {
                        println!("Computer attack commitments count: {}", commitments_count);
                        println!("Computer targeted ({}, {})", attack_x, attack_y);
                    }
                    if hit {
                        println!("\nHit!");
                        // record the hit on the player's grid
                        player_game.record_hit(attack_x, attack_y);
                        
                        // check if all ships are sunk
                        if player_game.all_ships_sunk() {
                            println!("Computer wins!");
                            break;
                        }
                    } else {
                        println!("\nMiss!");
                    }
                } else {
                    println!("Invalid attack! Proof verification failed...");
                    if verbose_mode {
                        println!("Proof validation failed for computer attack ({}, {})", attack_x, attack_y);
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

fn get_bool(prompt: &str) -> bool {
    loop {
        let value = get_input(prompt);
        match value {
            0 => return false,
            1 => return true,
            _ => println!("Please enter 1 or 0"),
        }
    }
}
