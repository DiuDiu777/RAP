// testcase for the path constraints analysis
fn main() {
    let x = 1;
    let mut _y = 10;
    let z = 0;
    if x < _y {
        _y += 1;
}
else{
   _y -= 1;
   if _y > z {
       _y -= 2;
   } else {
       _y += 2;
   }
}
}