pub fn flip_endian<T: Clone>(data: &[T]) -> Vec<T> {
    data.chunks(8)
        .flat_map(|c| c.iter().rev())
        .cloned()
        .collect()
}
