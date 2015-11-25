// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

int main()
{
    int a;
    assume(a > 1);

    // Prevent considering states with overflow
    // value_max^2 > a_max
    // (value_max + 1)^2 = INT32_MAX
    // therefore
    // value_max = sqrt(INT32_MAX) -1
    // therefore
    // a_max < INT32_MAX -2*sqrt(INT32_MAX) + 1
    // a_max < 2147390966.09999789602932182242 (approximate)
    assume(a < 2147390966);

    assume(a > 60000);

    int counter; counter=1;
    int value; value=1;
    while ( counter*counter <= a )
        invariant ( value*value <= a),
        invariant ( ((counter*counter > a) && value+1 == counter) || value == counter ),
        invariant ( value >= 1),
        invariant ( counter >= 1),
        invariant ( value < 46340),
        invariant ( counter < 46340),
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
