pub mod assert;
pub mod cs;

pub(in super::super) fn debug_success(name: &str, i: usize, frequency: usize) {
    if i % frequency == frequency - 1 {
        println!("{} tests {} to {} have passed", name, i + 1 - frequency, i);
    }
}
