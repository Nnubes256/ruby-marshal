require "test_harness"

class DumpTest
    def initialize(a)
        @a = a
    end
end

x1 = DumpTest.new(1)
x2 = DumpTest.new(2)
x3 = DumpTest.new(3)

generate_test_vector([
    x1, # full
    x1, # link
    x1, # link
    x1, # link

    x2, # full
    x2, # link
    x2, # link

    x1, # link

    x3, # full,
    x3, # link
    x3, # link,

    # everything from here on is a link
    x1,
    x2,
    x3,
    x2,
    x1
])