require "test_harness"

root = []
a = root

for i in 1..1024
    b = []
    a.push(b)
    a = b
end

generate_test_vector(root)