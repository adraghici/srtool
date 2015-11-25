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

    int counter; counter=1;
    int value; value=1;
    while ( counter*counter <= a )
        candidate_invariant ( value*value <= a),
        candidate_invariant ( ((counter*counter > a) && value+1 == counter) || value == counter ),
        candidate_invariant ( value >= 1),
        candidate_invariant ( counter >= 1),
        candidate_invariant ( value < 300),
        candidate_invariant ( counter < 300),
        candidate_invariant ( value*value <= counter*counter),

        candidate_invariant ( value*value < counter*counter),
        candidate_invariant ( value < 200),
        candidate_invariant ( counter < 200),
        candidate_invariant ( ((counter*counter > a) && value == counter) || value == counter )
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
