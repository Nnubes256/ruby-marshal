require "test_harness"

class DumpTest
    def initialize(a, id)
        @a = a
        @id = id
    end
end

x1_1 = DumpTest.new(nil, 1)
x1_2 = DumpTest.new(x1_1, 2)
x1_3 = DumpTest.new(x1_2, 3)

x2_1 = DumpTest.new(nil, -1)
x2_2 = DumpTest.new(x2_1, -2)
x2_3 = DumpTest.new(x2_2, -3)

generate_test_vector([
    x1_3, # full + full + full
    x1_3, # link + link + link

    x2_1, # full
    x2_2, # full + link
    x2_3, # full + link + link
    x2_3, # link + link + link
])