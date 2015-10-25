
function test($module = "test\Spec.hs") {
    cabal exec runhaskell -- -- -isrc -itest $module
}

if ([string]::isNullOrEmpty($args[0])) {
    test
} else {
    test $args[0]
}