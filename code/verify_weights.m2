-- Chenyang Zhao Master Thesis
-- Macaulay2 verification of the torus weights in the tangent space of Hilb^{n,n+1}(A^2) at monomial nested fixed points.
-- The script computes the compatibility kernel: ker( Hom(I,R/I) ++ Hom(J,R/J) --> Hom(I,R/J) )
-- Using monomial generators, monomial bases and the lcm syzygies among generators of a monomial ideal in two variables. It then compares the resulting weight multiset with the row-and-column shortening rule.
-- Convention: the geometric torus acts by (q,t).(a,b)=(qa,tb). If a map sends a source monomial x^i y^j to a target monomial x^r y^s, its weight is (i-r,j-s), written additively.
-- We first print one concrete showcase example, then run the full finite check. To change the bound, edit MAXSIZE at the bottom of the file.

----------------------------------------
-- small list and exponent utilities
----------------------------------------

-- Monomials are represented only by their exponent pairs.
-- For example {2,1} means x^2 y.
-- Some of the small helpers below could be replaced by built-in Macaulay2 list or hash-table operations.
-- They are kept explicit so that the code mirrors the mathematics used in the thesis: exponent addition, monomial divisibility, sparse linear equations and weight multisets.
vwContains = (L, x) -> (
    found := false;
    for y in L do if y == x then found = true;
    found
);

-- This could be replaced by unique L, but the explicit version makes the multiset comparison below self-contained.
uniqueList = L -> (
    ans := {};
    for x in L do if not vwContains(ans, x) then ans = append(ans, x);
    ans
);

addExp = (a,b) -> {a#0 + b#0, a#1 + b#1};
subExp = (a,b) -> {a#0 - b#0, a#1 - b#1};

-- lcmExp and dividesExp are the exponent-vector versions of lcm(x^a y^b, x^c y^d) and monomial divisibility.
lcmExp = (a,b) -> {
    if a#0 > b#0 then a#0 else b#0,
    if a#1 > b#1 then a#1 else b#1
};

dividesExp = (a,b) -> (a#0 <= b#0 and a#1 <= b#1);

expKey = e -> concatenate(toString(e#0), ",", toString(e#1));
varKey = v -> concatenate(v#0, ":", toString(v#1), ":", expKey(v#2));

-- Rows are stored sparsely as hash tables: column index -> coefficient.
-- Macaulay2 can build matrices directly, but sparse rows keep the syzygy and compatibility equations visible as equations in named variables.
nonzeroRow = rowVec -> (
    ok := false;
    for a in rowVec do if a != 0 then ok = true;
    ok
);

addToRow = (row, col, coeff) -> (
    if row#?col then row#col = row#col + coeff else row#col = coeff;
);

counterAdd = (H, key, amount) -> (
    if H#?key then H#key = H#key + amount else H#key = amount;
);

-- These counters are multisets of weights. We need multiplicities, not just the set of weights that occur.
-- The counter language is used to match the statement of the theorem: each torus weight appears with a multiplicity.
counterGet = (H, key) -> if H#?key then H#key else 0;

counterEquals = (A,B) -> (
    allKeys := uniqueList((keys A) | (keys B));
    ok := true;
    for k in allKeys do if counterGet(A,k) != counterGet(B,k) then ok = false;
    ok
);

counterToString = H -> (
    s := "{";
    first := true;
    for k in keys H do (
        if first then first = false else s = concatenate(s, ", ");
        s = concatenate(s, k, " => ", toString(H#k));
    );
    concatenate(s, "}")
);

counterToSortedString = H -> (
    s := "{";
    first := true;
    for k in sort keys H do (
        if first then first = false else s = concatenate(s, ", ");
        s = concatenate(s, k, " => ", toString(H#k));
    );
    concatenate(s, "}")
);

----------------------------------------
-- partitions and Young diagrams
----------------------------------------

vwPartitions = (n, maxPart) -> (
    if n == 0 then {{}} else (
        m := if maxPart > n then n else maxPart;
        ans := {};
        -- Build partitions in nonincreasing order. The explicit offset loop avoids relying on descending for-loop syntax.
        for offset from 0 to m - 1 do (
            first := m - offset;
            rest := n - first;
            if rest == 0 then ans = append(ans, {first}) else (
                nextMax := if first < rest then first else rest;
                for p in vwPartitions(rest, nextMax) do ans = append(ans, prepend(first, p));
            );
        );
        ans
    )
);

partitionsOf = n -> vwPartitions(n,n);

diagram = part -> (
    D := {};
    if #part > 0 then (
        for j from 0 to #part - 1 do (
            if part#j > 0 then for i from 0 to part#j - 1 do D = append(D, {i,j});
        );
    );
    D
);

-- For a monomial ideal I_lambda, the boxes of the Young diagram are exactly the monomial basis of R/I_lambda.
quotientBasis = part -> diagram part;

corners = part -> (
    D := diagram part;
    ans := {};
    for s in D do (
        if not vwContains(D, {s#0 + 1, s#1}) and not vwContains(D, {s#0, s#1 + 1}) then
            ans = append(ans, s);
    );
    ans
);

removeCorner = (part, c) -> (
    out := {};
    if #part > 0 then (
        for j from 0 to #part - 1 do (
            out = append(out, if j == c#1 then part#j - 1 else part#j);
        );
    );
    n := #out;
    while n > 0 and out#(n-1) == 0 do n = n - 1;
    trimmed := {};
    if n > 0 then for j from 0 to n - 1 do trimmed = append(trimmed, out#j);
    trimmed
);

armLeg = (part, s) -> (
    D := diagram part;
    i := s#0;
    j := s#1;
    a := 0;
    while vwContains(D, {i + a + 1, j}) do a = a + 1;
    ell := 0;
    while vwContains(D, {i, j + ell + 1}) do ell = ell + 1;
    {a, ell}
);

minimalGenerators = part -> (
    D := diagram part;
    maxI := if #part == 0 then 0 else part#0;
    maxJ := #part;
    candidates := {};
    -- A minimal generator is just outside the diagram, but its left and lower neighbours, when present, are still inside the diagram.
    for i from 0 to maxI do (
        for j from 0 to maxJ do (
            if not vwContains(D, {i,j}) then (
                if (i == 0 or vwContains(D, {i-1,j})) and (j == 0 or vwContains(D, {i,j-1})) then
                    candidates = append(candidates, {i,j});
            );
        );
    );
    -- Remove candidates divisible by another candidate, leaving the minimal monomial generators of I_lambda.
    minimal := {};
    for g in candidates do (
        dominated := false;
        for h in candidates do (
            if h != g and dividesExp(h,g) then dominated = true;
        );
        if not dominated then minimal = append(minimal, g);
    );
    minimal
);

----------------------------------------
-- linear equations for Hom of a monomial ideal
----------------------------------------

-- Construct the linear equations defining Hom_R(I,R/K).
-- A map I -> R/K is determined by the images of the minimal generators of I, but these images must satisfy the lcm-syzygies among those generators:
-- (lcm(g_i,g_j)/g_i) phi(g_i) - (lcm(g_i,g_j)/g_j) phi(g_j) = 0 in R/K.
-- Each possible coefficient of phi(g_i) is one variable, and each coefficient of each syzygy output gives one linear row.
homSyzygyRows = (prefix, gens, basis, varIndex) -> (
    rows := {};
    if #gens >= 2 then (
        for i from 0 to #gens - 2 do (
            for j from i + 1 to #gens - 1 do (
                gi := gens#i;
                gj := gens#j;
                L := lcmExp(gi, gj);
                ri := subExp(L, gi);
                rj := subExp(L, gj);
                byOutput := new MutableHashTable;
                for b in basis do (
                    -- If phi(g_i) contains the basis monomial b, then multiplying by lcm(g_i,g_j)/g_i sends b to out1.
                    out1 := addExp(b, ri);
                    if vwContains(basis, out1) then (
                        k1 := expKey(out1);
                        if not byOutput#?k1 then byOutput#k1 = new MutableHashTable;
                        row1 := byOutput#k1;
                        addToRow(row1, varIndex#(varKey({prefix, i, b})), 1);
                    );
                    -- The contribution from phi(g_j) has the opposite sign in the lcm-syzygy.
                    out2 := addExp(b, rj);
                    if vwContains(basis, out2) then (
                        k2 := expKey(out2);
                        if not byOutput#?k2 then byOutput#k2 = new MutableHashTable;
                        row2 := byOutput#k2;
                        addToRow(row2, varIndex#(varKey({prefix, j, b})), -1);
                    );
                );
                for k in keys byOutput do rows = append(rows, byOutput#k);
            );
        );
    );
    rows
);

----------------------------------------
-- kernel calculation and formula calculation
----------------------------------------

-- Compute the torus-weight multiset of the actual nested tangent space.
-- Here big = lambda and small = mu = lambda minus one corner. This function builds the compatibility kernel: ker( Hom(I_big,R/I_big) ++ Hom(I_small,R/I_small) -> Hom(I_big,R/I_small) ).
-- The output is a multiset of additive weights, such as "2,-1" for q^2 t^{-1}.
kernelWeightMultiset = (big, small) -> (
    gensBig := minimalGenerators big;
    basisBig := quotientBasis big;
    gensSmall := minimalGenerators small;
    basisSmall := quotientBasis small;

    -- Variables for alpha: I_big -> R/I_big and beta: I_small -> R/I_small. A variable {"alpha", i, b} is the coefficient of monomial b in the image of the i-th minimal generator of I_big.
    variables := {};
    if #gensBig > 0 then (
        for i from 0 to #gensBig - 1 do for b in basisBig do
            variables = append(variables, {"alpha", i, b});
    );
    if #gensSmall > 0 then (
        for i from 0 to #gensSmall - 1 do for b in basisSmall do
            variables = append(variables, {"beta", i, b});
    );

    varIndex := new MutableHashTable;
    if #variables > 0 then for i from 0 to #variables - 1 do varIndex#(varKey(variables#i)) = i;

    rows := {};
    rows = rows | homSyzygyRows("alpha", gensBig, basisBig, varIndex);
    rows = rows | homSyzygyRows("beta", gensSmall, basisSmall, varIndex);

    -- Compatibility pi alpha(g)=beta(g) for each minimal generator g of I_big. Since I_big is contained in I_small, every generator g of I_big is a monomial multiple of some generator h of I_small.  If g = x^r y^s h, then beta(g) is x^r y^s beta(h).
    if #gensBig > 0 then (
        for i from 0 to #gensBig - 1 do (
            g := gensBig#i;
            chosen := -1;
            chosenGen := {};
            if #gensSmall > 0 then (
                for j from 0 to #gensSmall - 1 do (
                    h := gensSmall#j;
                    if chosen == -1 and dividesExp(h,g) then (
                        chosen = j;
                        chosenGen = h;
                    );
                );
            );
            if chosen == -1 then error(concatenate("No generator of I_small divides generator ", toString g));
            r := subExp(g, chosenGen);
            for c in basisSmall do (
                row := new MutableHashTable;
                -- Coefficient of c in pi alpha(g).
                addToRow(row, varIndex#(varKey({"alpha", i, c})), 1);
                -- Coefficient of c in beta(g). If g = x^r y^s h, then this comes from the coefficient of c/(x^r y^s) in beta(h).
                b := subExp(c, r);
                if b#0 >= 0 and b#1 >= 0 and vwContains(basisSmall, b) then
                    addToRow(row, varIndex#(varKey({"beta", chosen, b})), -1);
                rows = append(rows, row);
            );
        );
    );

    -- Group variables by torus weight. If a variable sends source monomial x^i y^j to target monomial x^r y^s, its additive weight is (i-r,j-s).
    varsByWeight := new MutableHashTable;
    weightsByKey := new MutableHashTable;
    if #variables > 0 then (
        for idx from 0 to #variables - 1 do (
            v := variables#idx;
            source := if v#0 == "alpha" then gensBig#(v#1) else gensSmall#(v#1);
            target := v#2;
            w := subExp(source, target);
            k := expKey(w);
            if not varsByWeight#?k then (
                varsByWeight#k = {};
                weightsByKey#k = w;
            );
            varsByWeight#k = append(varsByWeight#k, idx);
        );
    );

    answer := new MutableHashTable;
    for k in keys varsByWeight do (
        cols := varsByWeight#k;
        relevantRows := {};
        -- The equations are homogeneous for the torus action, so each weight can be treated separately. For this weight block, dim kernel = number of variables - rank of equations.
        for row in rows do (
            rowVec := {};
            for p from 0 to #cols - 1 do (
                col := cols#p;
                rowVec = append(rowVec, if row#?col then row#col else 0);
            );
            if nonzeroRow rowVec then relevantRows = append(relevantRows, rowVec);
        );
        rnk := if #relevantRows == 0 then 0 else rank matrix(QQ, relevantRows);
        dim := #cols - rnk;
        if dim != 0 then answer#k = dim;
    );
    answer
);

-- Compute the predicted weight multiset from the row-and-column shortening rule for arm-leg arrows.
formulaWeightMultiset = (big, corner) -> (
    ci := corner#0;
    cj := corner#1;
    answer := new MutableHashTable;
    for s in diagram big do (
        i := s#0;
        j := s#1;
        al := armLeg(big, s);
        a := al#0;
        ell := al#1;
        -- Ordinary Hilbert-scheme arm-leg weights: horizontal q^(a+1)t^(-ell) and vertical q^(-a)t^(ell+1).
        w1 := {a + 1, -ell};
        w2 := {-a, ell + 1};
        -- Nested condition: shorten horizontal arrows left of the corner by one q, and vertical arrows below the corner by one t.
        if j == cj and i < ci then w1 = {a, -ell};       -- boxes left of the corner
        if i == ci and j < cj then w2 = {-a, ell};       -- boxes below the corner
        counterAdd(answer, expKey(w1), 1);
        counterAdd(answer, expKey(w2), 1);
    );
    answer
);

-- Print one concrete example before the full loop. This is the less symmetric example lambda=(3,2,1), with the middle corner removed.
showcaseExample = () -> (
    big := {3,2,1};
    corner := {1,1};
    small := removeCorner(big, corner);
    gensBig := minimalGenerators big;
    basisBig := quotientBasis big;
    gensSmall := minimalGenerators small;
    basisSmall := quotientBasis small;
    computed := kernelWeightMultiset(big, small);
    predicted := formulaWeightMultiset(big, corner);

    print "Showcase example:";
    print concatenate("lambda = ", toString big, ", corner = ", toString corner, ", mu = ", toString small);
    print concatenate("D(lambda) = ", toString basisBig);
    print concatenate("D(mu) = ", toString basisSmall);
    print concatenate("minimal generators of I_lambda = ", toString gensBig);
    print concatenate("minimal generators of I_mu = ", toString gensSmall);
    print concatenate("kernel side      = ", counterToSortedString computed);
    print concatenate("modification side = ", counterToSortedString predicted);
    print concatenate("agree = ", toString counterEquals(computed, predicted));
);

-- Compare the two constructions for all partitions up to maxSize and for every removable corner. A failure prints both multisets.
verify = maxSize -> (
    total := 0;
    for n from 1 to maxSize do (
        for part in partitionsOf n do (
            for c in corners part do (
                small := removeCorner(part, c);
                computed := kernelWeightMultiset(part, small);
                predicted := formulaWeightMultiset(part, c);
                total = total + 1;
                if not counterEquals(computed, predicted) then (
                    print "FAILED";
                    print concatenate("partition = ", toString part, ", corner = ", toString c, ", small = ", toString small);
                    print concatenate("computed  = ", counterToSortedString computed);
                    print concatenate("predicted = ", counterToSortedString predicted);
                    error "Verification failed.";
                );
            );
        );
    );
    print concatenate("All tests passed for |lambda| <= ", toString maxSize, ".");
    print concatenate("Checked ", toString total, " nested fixed points.");
);

MAXSIZE = 16;
showcaseExample();
verify MAXSIZE;
