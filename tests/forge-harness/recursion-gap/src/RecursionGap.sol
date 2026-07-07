// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// Stage-0 gap fixture for docs/function-boundary-refactor-plan.md.
// solc/Forge accept and run these; the current Lean elaboration inlines
// all internal-linkage calls with defaultInternalCallInlineFuel = 64 and
// silently REJECTS both a genuinely recursive function and a static call
// chain deeper than 64 (toCoreContract? = none => the whole contract fails
// to elaborate).  The Lean witnesses in the manifest pin that rejection
// today; they flip to the real values at stage 5 of the refactor.
contract RecursionGapHarnessTarget {
    // (a) genuine recursion: factorial(5) = 120.
    function factorial(uint256 n) public pure returns (uint256) {
        if (n <= 1) {
            return 1;
        }
        return n * factorial(n - 1);
    }

    // (a') recursion whose runtime depth itself exceeds 64: sumTo(70) = 2485.
    function sumTo(uint256 n) public pure returns (uint256) {
        if (n == 0) {
            return 0;
        }
        return n + sumTo(n - 1);
    }

    // (b) static (non-recursive) call chain of depth 70 > 64.
    //     step0() calls step1() ... step69() calls step70(); each
    //     inner step adds 1, so step0() = 70.
    function deepChain() external pure returns (uint256) {
        return step0();
    }

    function step0() internal pure returns (uint256) {
        return 1 + step1();
    }

    function step1() internal pure returns (uint256) {
        return 1 + step2();
    }

    function step2() internal pure returns (uint256) {
        return 1 + step3();
    }

    function step3() internal pure returns (uint256) {
        return 1 + step4();
    }

    function step4() internal pure returns (uint256) {
        return 1 + step5();
    }

    function step5() internal pure returns (uint256) {
        return 1 + step6();
    }

    function step6() internal pure returns (uint256) {
        return 1 + step7();
    }

    function step7() internal pure returns (uint256) {
        return 1 + step8();
    }

    function step8() internal pure returns (uint256) {
        return 1 + step9();
    }

    function step9() internal pure returns (uint256) {
        return 1 + step10();
    }

    function step10() internal pure returns (uint256) {
        return 1 + step11();
    }

    function step11() internal pure returns (uint256) {
        return 1 + step12();
    }

    function step12() internal pure returns (uint256) {
        return 1 + step13();
    }

    function step13() internal pure returns (uint256) {
        return 1 + step14();
    }

    function step14() internal pure returns (uint256) {
        return 1 + step15();
    }

    function step15() internal pure returns (uint256) {
        return 1 + step16();
    }

    function step16() internal pure returns (uint256) {
        return 1 + step17();
    }

    function step17() internal pure returns (uint256) {
        return 1 + step18();
    }

    function step18() internal pure returns (uint256) {
        return 1 + step19();
    }

    function step19() internal pure returns (uint256) {
        return 1 + step20();
    }

    function step20() internal pure returns (uint256) {
        return 1 + step21();
    }

    function step21() internal pure returns (uint256) {
        return 1 + step22();
    }

    function step22() internal pure returns (uint256) {
        return 1 + step23();
    }

    function step23() internal pure returns (uint256) {
        return 1 + step24();
    }

    function step24() internal pure returns (uint256) {
        return 1 + step25();
    }

    function step25() internal pure returns (uint256) {
        return 1 + step26();
    }

    function step26() internal pure returns (uint256) {
        return 1 + step27();
    }

    function step27() internal pure returns (uint256) {
        return 1 + step28();
    }

    function step28() internal pure returns (uint256) {
        return 1 + step29();
    }

    function step29() internal pure returns (uint256) {
        return 1 + step30();
    }

    function step30() internal pure returns (uint256) {
        return 1 + step31();
    }

    function step31() internal pure returns (uint256) {
        return 1 + step32();
    }

    function step32() internal pure returns (uint256) {
        return 1 + step33();
    }

    function step33() internal pure returns (uint256) {
        return 1 + step34();
    }

    function step34() internal pure returns (uint256) {
        return 1 + step35();
    }

    function step35() internal pure returns (uint256) {
        return 1 + step36();
    }

    function step36() internal pure returns (uint256) {
        return 1 + step37();
    }

    function step37() internal pure returns (uint256) {
        return 1 + step38();
    }

    function step38() internal pure returns (uint256) {
        return 1 + step39();
    }

    function step39() internal pure returns (uint256) {
        return 1 + step40();
    }

    function step40() internal pure returns (uint256) {
        return 1 + step41();
    }

    function step41() internal pure returns (uint256) {
        return 1 + step42();
    }

    function step42() internal pure returns (uint256) {
        return 1 + step43();
    }

    function step43() internal pure returns (uint256) {
        return 1 + step44();
    }

    function step44() internal pure returns (uint256) {
        return 1 + step45();
    }

    function step45() internal pure returns (uint256) {
        return 1 + step46();
    }

    function step46() internal pure returns (uint256) {
        return 1 + step47();
    }

    function step47() internal pure returns (uint256) {
        return 1 + step48();
    }

    function step48() internal pure returns (uint256) {
        return 1 + step49();
    }

    function step49() internal pure returns (uint256) {
        return 1 + step50();
    }

    function step50() internal pure returns (uint256) {
        return 1 + step51();
    }

    function step51() internal pure returns (uint256) {
        return 1 + step52();
    }

    function step52() internal pure returns (uint256) {
        return 1 + step53();
    }

    function step53() internal pure returns (uint256) {
        return 1 + step54();
    }

    function step54() internal pure returns (uint256) {
        return 1 + step55();
    }

    function step55() internal pure returns (uint256) {
        return 1 + step56();
    }

    function step56() internal pure returns (uint256) {
        return 1 + step57();
    }

    function step57() internal pure returns (uint256) {
        return 1 + step58();
    }

    function step58() internal pure returns (uint256) {
        return 1 + step59();
    }

    function step59() internal pure returns (uint256) {
        return 1 + step60();
    }

    function step60() internal pure returns (uint256) {
        return 1 + step61();
    }

    function step61() internal pure returns (uint256) {
        return 1 + step62();
    }

    function step62() internal pure returns (uint256) {
        return 1 + step63();
    }

    function step63() internal pure returns (uint256) {
        return 1 + step64();
    }

    function step64() internal pure returns (uint256) {
        return 1 + step65();
    }

    function step65() internal pure returns (uint256) {
        return 1 + step66();
    }

    function step66() internal pure returns (uint256) {
        return 1 + step67();
    }

    function step67() internal pure returns (uint256) {
        return 1 + step68();
    }

    function step68() internal pure returns (uint256) {
        return 1 + step69();
    }

    function step69() internal pure returns (uint256) {
        return 1 + step70();
    }

    function step70() internal pure returns (uint256) {
        return 0;
    }
}
