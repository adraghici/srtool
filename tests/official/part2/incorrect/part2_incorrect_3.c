// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"


int main()
{
    int input;
    int input_copy;
    int output; output=0;

    input_copy = input;

    int count; count = 32; // width of int

    while (count > 0)
    //bound(32)
    {
        output = output | ( input_copy & 1 );
        input_copy = input_copy >> 1;
        count = count -1;
        output = output << 1; // BUG: Doing the shift here causes one too many shifts
    }

    // output now contains the bits of input
    // in reverse order

    // check this property holds
    count = 0;
    int value; value = 0;
    while ( count < 32)
    //bound(32)
    {
        value = (output >> (31 - count)) & 1;
        assert( ((input >> count ) & 1) == value);
        count = count + 1;
    }

    // Reverse the bits in output to get back original
    count = 32;
    input_copy = output;
    output = 0;
    while (count > 0)
    //bound(32)
    {
        output = output << 1;
        output = output | ( input_copy & 1 );
        input_copy = input_copy >> 1;
        count = count -1;
    }

    assert(output == input);
  return 0;
}
