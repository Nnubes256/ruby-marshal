fn main() {
    // ruby: Marshal.dump({:thing1 => 1, :thing2 => "hello", :thing3 => [1,2,3]})
    let input: &[u8] = &[
        0x04, 0x08, 0x7b, 0x08, 0x3a, 0x0b, 0x74, 0x68, 0x69, 0x6e, 0x67, 0x31, 0x69, 0x06, 0x3a,
        0x0b, 0x74, 0x68, 0x69, 0x6e, 0x67, 0x32, 0x49, 0x22, 0x0a, 0x68, 0x65, 0x6c, 0x6c, 0x6f,
        0x06, 0x3a, 0x0d, 0x65, 0x6e, 0x63, 0x6f, 0x64, 0x69, 0x6e, 0x67, 0x22, 0x0e, 0x53, 0x68,
        0x69, 0x66, 0x74, 0x5f, 0x4a, 0x49, 0x53, 0x3a, 0x0b, 0x74, 0x68, 0x69, 0x6e, 0x67, 0x33,
        0x5b, 0x08, 0x69, 0x06, 0x69, 0x07, 0x69, 0x08,
    ];
    let out = ruby_marshal::from_bytes::<ruby_marshal::value::ValueHL>(input);
    println!("{:#?}", out);
}
