# Possible bugs I should investigate in the java implem

1. state intervals:
    * remove all but seems incorrect to me:
        interval [0 .. 5]
        remove all but 7 (there is an assert stmt, but this is pretty weak)
    * remove above can reopen interval:
        interval [0 .. 4]
        remove below 5
        remove above 7
    * remove below can reopen interval:
        interval [0 .. 4]
        remove above -1
        remove below -5
2. Lazy sparse set is incorrect (I think)
    when the LSS lazily creates the SS, is created it uses the current min and
    max values to avoid intializing a large array (that's ok). Also, the LSS
    maintains a flag to avoid recreating the SS later on. However, it might
    be the case that upon restore_state() the LSS still uses the SS it has
    created, but that SS is too small to hold all values of the actual domain.

    Example:
        LSS = [0..=10]
        save state
        remove below 3 -> min is now 3 (LSS = [3..=10])
        remove above 7 -> max is now 7 (LSS = [3..=7])
        remove 5       -> creates the SS {3, 4, 5, 6, 7}
                       -> punches a hole in the domain
                       -> LSS = SS = {3,4,6,7}
        restore state  -> LSS is still a SS and the represented domain is now
                       -> {3, 4, 5, 6, 7} which is not equivalent to the original
                       -> domain [0..=10]