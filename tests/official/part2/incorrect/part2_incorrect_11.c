// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

int main()
{
    int a;
    assume(a > 1);

    // Prevent considering states with overflow
    // value_max^2 > a_max
    // (value_max + 1)^2 = UINT32_MAX
    // therefore
    // value_max = sqrt(UINT32_MAX) -1
    // therefore
    // a_max < UINT32_MAX -2*sqrt(UINT32_MAX) + 1
    // a_max < 4294836224.00001525878906338818 (approximate)
    // assume(a < 4294836224); // THE PARSER CAN'T HANDLE THIS!

    // Okay lets just be overly restrictive instead
    assume( a < 65535);

    // force many iterations
    assume( a > 60000);

    int counter; counter=1;
    int value; value=1;
    while ( counter*counter <= a )
        invariant ( value*value <= a),
        invariant ( ((counter*counter > a) && value+1 == counter) || value == counter ),
        invariant ( value >= 1),
        invariant ( counter >= 1),
        invariant ( value < 300),
        invariant ( counter < 300),
        invariant ( value*value <= counter*counter)
    {
        counter = counter + 1;
        if (counter*counter <= a)
        {
            value = counter;
        }
    }

    assert( (value*value) == a);
    //assert( ((value+1)*(value+1)) > a);
  return 0;
}
