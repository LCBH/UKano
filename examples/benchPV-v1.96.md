The following table is not up to date concerning heuristics greedy/default/syntax. Please only refers to WA column
and consider FO columns as 'user-defined' column.

| Protocol    | Better time (total) | Time for WA | Time for FO (greedy) | Time for FO (default) | Time for FO (syntax)  | Time for FO (user-defined) |
|:------------|:-------------:|:-------------------:|:-------------------:|:---------------------:|:--------------------:|:---------------------------|
| Hash-Lock      | 0.03s  | 0.01s | 0.02s  | 0.02s   | 0.02s   | --    |
| Fixed LAK      | 0.03s  | 0.01s | 0.02s  | 0.02s   | 0.02s   | --    |
| BAC            | 70.65s | 0.09s | 66.56s | 128.03s | 132.24s | --    |
| BAC+AA+PA      |1290.46s| 2.11s |1288.46s| 6111.04s| 6017.32s| --    |
| BAC+PA+AA      | 70.65s | 1.86s |1151.84s| 7134.94s| 6956.75s| --    |
| PACE with tags | :curly_loop:   |488.11s| :x:    | :x:     | :curly_loop: | --    |
| DAA simplified [HBD17]| 0.12s |0.02s|0.10s| 0.10s  | 0.10s   | --    |
| DAA sign       | 89.24s | 0.08s | :x:    | :x:     | 89.16s  | --    |
| DAA join       | 21.84s | 0.01s | 21.83s | 22.25s  | 60.07s  | --    |
| abcdh (irma)   | :curly_loop: | 62524.78s|:curly_loop:| :curly_loop: | :curly_loop:  | :curly_loop: |
