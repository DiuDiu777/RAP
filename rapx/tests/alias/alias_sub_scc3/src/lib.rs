
#![allow(unused)]

enum Selector {
    First,
    Second,
}

// Expected result: (r,x) (r,z)
fn foo<'a>(x: &'a i32, y: &'a i32, z: &'a i32, choice: Selector) -> &'a i32 {
    let mut r = x; 
    let mut q = z; 

    // [Outer SCC]: Configuration Phase
    loop {
        // Defines the 'Source' of the pipeline based on 'choice'
        // This is the "Input Valve"
        let mut p = match choice {
            Selector::First => y,   // Path A: Source is 'y' (Polluted/Distractor)
            Selector::Second => x,  // Path B: Source is 'x' (Clean/Target)
        };

        // [Inner SCC]: Propagation Phase (The Pipeline)
        loop {
            if random() { break; }
            r = match choice {
                Selector::First => x,      
                Selector::Second => p, 
            };
            p = z;
        }
        if random() { break; }
    }
    r
}


fn random() -> bool {
    use std::time::{SystemTime, UNIX_EPOCH};
    let start = SystemTime::now();
    let since_the_epoch = start.duration_since(UNIX_EPOCH).expect("Time went backwards");
    since_the_epoch.subsec_nanos() % 2 == 0
}