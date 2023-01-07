require "test_harness"

class DumpTest
    def initialize(a)
        @a = a
    end
end

# userdef example from Ruby documentation
class MyObj
    def initialize name, version, data
        @name    = name
        @version = version
        @data    = data
    end
  
    def _dump level
        [@name, @version].join ':'
    end
  
    def self._load args
        new(*args.split(':'))
    end
end

x_nil = nil
x_true = true
x_false = false
x_int = 42
x_float = Math::PI
x_array = [1, 2, 3]
x_hash = {:a => 1, :b => 2, :c => 3}
x_symbol = :hello
x_ivar = "hello"
x_regexp = /foobar/i
x_bytestring = Marshal.dump(nil)
x_classref = Math::DomainError
x_moduleref = Enumerable
x_object = DumpTest.new(1)
x_userdef = MyObj.new("ruby-marshal", "1.0", nil)

generate_test_vector([
    x_nil,
    x_true,
    x_false,
    x_int,
    x_float,
    x_array,
    x_hash,
    x_symbol,
    x_ivar,
    x_regexp,
    x_classref,
    x_moduleref,
    x_object,
    x_userdef,
    x_bytestring,

    x_nil,
    x_true,
    x_false,
    x_int,
    x_float,
    x_array,
    x_hash,
    x_symbol,
    x_ivar,
    x_regexp,
    x_classref,
    x_moduleref,
    x_object,
    x_userdef,
    x_bytestring,

    x_nil,
    x_true,
    x_false,
    x_int,
    x_float,
    x_array,
    x_hash,
    x_symbol,
    x_ivar,
    x_regexp,
    x_classref,
    x_moduleref,
    x_object,
    x_userdef,
    x_bytestring,
])