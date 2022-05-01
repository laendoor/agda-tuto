-- Exercise finite-|-assoc (stretch)

-- In the beginning, we know nothing.
-- On the first day
(0 + n) + p = (n) + p
            = n + p
            = (n + p)
            = 0 + (n + p)

-- On the second day
(0 + n) + p = 0 + (n + p)
(1 + n) + p = (1 + 0 + n) + p
            = 1 + (0 + n) + p
            = 1 + (n + p)

-- On the third day
(0 + n) + p = 0 + (n + p)
(1 + n) + p = 1 + (n + p)
(2 + n) + p = (1 + 1 + n) + p
            = 1 + (1 + n) + p
            = 1 + 1 + (n + p)
            = 2 + (n + p)

-- On the fourth day
(0 + n) + p = 0 + (n + p)
(1 + n) + p = 1 + (n + p)
(2 + n) + p = 2 + (n + p)
(3 + n) + p = (1 + 2 + n) + p
            = 1 + (2 + n) + p
            = 1 + 2 + (n + p)
            = 3 + (n + p)

