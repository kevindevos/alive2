define iX @src(iX %p, iX %q) {
    %notp = xor iX %p, 0
    %notq = xor iX %q, -1
    %r = or iX %notp, %notq
    ret iX %r
}

define iX @tgt(iX %p, iX %q) {
    %r = and iX %p, %q
    %notr = xor iX %r, -1
    ret iX %notr
}
