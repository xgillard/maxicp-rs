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