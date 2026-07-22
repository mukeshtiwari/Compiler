#include <cassert>
#include <cstring>
#include <fstream>
#include <ios>
#include <limits>
#include <memory>

using uint = unsigned int;
static_assert(sizeof(uint) == 4);

extern "C" void f(unsigned char* in, uint insize, unsigned char* out, uint outsize);

int main(int argc, char const* argv[]) {
    assert(argc == 3);

    uint const outsize = 10;
    std::size_t const out_bytes = 32 * static_cast<std::size_t>(outsize);
    std::unique_ptr<unsigned char[]> in;
    std::unique_ptr<unsigned char[]> out;
    uint insize = 0;

    {
        std::ifstream in_file(argv[1], std::ios::binary | std::ios::ate);
        assert(in_file.good());
        auto const end = in_file.tellg();
        assert(end >= 0);
        std::size_t const in_bytes = static_cast<std::size_t>(end);
        assert(in_bytes % 32 == 0);
        assert(in_bytes / 32 <= std::numeric_limits<uint>::max());
        insize = static_cast<uint>(in_bytes / 32);
        in_file.seekg(0, std::ios::beg);
        in.reset(new unsigned char[in_bytes]);
        in_file.read(reinterpret_cast<char*>(in.get()), static_cast<std::streamsize>(in_bytes));
        assert(in_file.gcount() == static_cast<std::streamsize>(in_bytes));
    }

    out.reset(new unsigned char[out_bytes]);
    std::memset(out.get(), 0, out_bytes);

    f(in.get(), insize, out.get(), outsize);

    {
        std::ofstream out_file(argv[2], std::ios::binary);
        out_file.write(reinterpret_cast<char const*>(out.get()), static_cast<std::streamsize>(out_bytes));
        assert(out_file.good());
    }

    return 0;
}
