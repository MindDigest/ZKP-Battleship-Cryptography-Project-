# ZKP BattleShip (BulletProofs and Snarks) 

all you really need is the main.rs and main_halo2_bulletproofs.rs

Codespace is a thing for this but its a work in progress and currently doens't work without your own efforts in setting it up

A battleship game using zero-knowledge proofs (zkSNARKs) to verify hits/misses without revealing ship positions.

## Implementation Notes

**Scope:**
- Full zkSNARK proof system (Halo2)
- Poseidon commitment scheme
- Bulletproofs for range proofs
- Complete game logic with cryptographic verification

**Simplifying Assumptions:**
- Game Logic is simplfied ease (i.e., no vertical/horizontal ships as ships are 1 unit/cell/position)
- Both players simulated locally (no network layer)
- In a real deployment: 
  - Each player would run on separate machines
  - Proofs would be transmitted over network
  - Server would coordinate game state
  - All cryptographic properties would remain identical

**Learning Objectives:**
- Understand zkSNARK circuit design
- Implement commitment schemes
- Practice Rust systems programming
- Explore zero-knowledge proof systems
