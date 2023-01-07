def generate_test_vector(object)
    File.write("#{File.basename($0, ".rb")}.bin", Marshal.dump(object))
end