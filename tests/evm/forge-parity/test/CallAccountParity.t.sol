// SPDX-License-Identifier: MIT
pragma solidity ^0.8.30;

interface CallAccountVm {
    struct Gas {
        uint64 gasLimit;
        uint64 gasTotalUsed;
        uint64 gasMemoryUsed;
        int64 gasRefunded;
        uint64 gasRemaining;
    }

    function ffi(string[] calldata command) external returns (bytes memory result);
    function lastCallGas() external view returns (Gas memory gas);
    function etch(address target, bytes calldata newRuntimeBytecode) external;
    function deal(address target, uint256 newBalance) external;
    function load(address target, bytes32 slot) external view returns (bytes32 value);
}

contract CallAccountParityTest {
    CallAccountVm internal constant vm = CallAccountVm(address(uint160(uint256(keccak256("hevm cheat code")))));

    address internal constant TARGET = 0x1000000000000000000000000000000000000001;
    address internal constant WORKER = 0x2000000000000000000000000000000000000002;
    address internal constant DELEGATE_LIB = 0x3000000000000000000000000000000000000003;
    uint256 internal constant GAS_LIMIT = 1_000_000;

    function testStaticcallMissingAccountParity() public {
        bytes memory code =
            hex"5f5f5f5f734000000000000000000000000000000000000004620f4240fa5f523d6020527340000000000000000000000000000000000000043f60405260605ff3";
        runCase("staticcall-missing-account", code);
    }

    function testDelegatecallMissingAccountParity() public {
        bytes memory code =
            hex"5f5f5f5f734000000000000000000000000000000000000004620f4240f45f523d6020527340000000000000000000000000000000000000043f60405260605ff3";
        runCase("delegatecall-missing-account", code);
    }

    function testCallcodeMissingAccountParity() public {
        bytes memory code =
            hex"5f5f5f5f5f734000000000000000000000000000000000000004620f4240f25f523d6020527340000000000000000000000000000000000000043f60405260605ff3";
        runCase("callcode-missing-account", code);
    }

    function testCallcodeValueMissingAccountInsufficientBalanceParity() public {
        bytes memory code =
            hex"5f5f5f5f6001734000000000000000000000000000000000000004620f4240f25f523d6020527340000000000000000000000000000000000000043f60405260605ff3";
        runCase("callcode-value-missing-account-insufficient-balance", code);
    }

    function testCallcodeValueMissingAccountSufficientBalanceParity() public {
        bytes memory code =
            hex"5f5f5f5f6001734000000000000000000000000000000000000004620f4240f25f523d6020527340000000000000000000000000000000000000043f60405260605ff3";
        runCaseWithBalance("callcode-value-missing-account-sufficient-balance", code, 2);
    }

    function testStaticcallMissingAccountClearsReturndataParity() public {
        bytes memory code =
            hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f15f523d6020525f5f5f5f734000000000000000000000000000000000000004620f4240fa6040523d6060527340000000000000000000000000000000000000043f60805260a05ff3";
        bytes memory accountCode = hex"602a5f5260205ff3";
        runCaseWithBalanceAndAccountCode("staticcall-missing-account-clears-returndata", code, 0, WORKER, accountCode);
    }

    function testCallcodeMissingAccountClearsReturndataParity() public {
        bytes memory code =
            hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f15f523d6020525f5f5f5f5f734000000000000000000000000000000000000004620f4240f26040523d6060527340000000000000000000000000000000000000043f60805260a05ff3";
        bytes memory accountCode = hex"602a5f5260205ff3";
        runCaseWithBalanceAndAccountCode("callcode-missing-account-clears-returndata", code, 0, WORKER, accountCode);
    }

    function testDelegatecallMissingAccountClearsReturndataParity() public {
        bytes memory code =
            hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f15f523d6020525f5f5f5f734000000000000000000000000000000000000004620f4240f46040523d6060527340000000000000000000000000000000000000043f60805260a05ff3";
        bytes memory accountCode = hex"602a5f5260205ff3";
        runCaseWithBalanceAndAccountCode("delegatecall-missing-account-clears-returndata", code, 0, WORKER, accountCode);
    }

    function testCallMissingAccountKeepsOutputAndClearsReturndataParity() public {
        bytes memory code =
            hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f1609960a052602060a05f5f5f734000000000000000000000000000000000000004620f4240f15f523d60205260a05160405260605ff3";
        bytes memory accountCode = hex"602a5f5260205ff3";
        runCaseWithBalanceAndAccountCode(
            "call-missing-account-keeps-output-clears-returndata", code, 0, WORKER, accountCode
        );
    }

    function testCallSelfValueInsufficientBalanceParity() public {
        bytes memory code = hex"366017575f5f60015f600130620f4240f15f5260205ff35b00";
        runCaseWithBalance("call-self-value-insufficient-balance", code, 0);
    }

    function testCallValueFailureKeepsOutputAndClearsReturndataParity() public {
        bytes memory code =
            hex"60425f5260205f5f5f6001732000000000000000000000000000000000000002620f4240f16020523d60405260605ff3";
        runCaseWithBalance("call-value-failure-keeps-output-clears-returndata", code, 0);
    }

    function testCallcodeValueInsufficientBalanceKeepsOutputAndClearsReturndataParity() public {
        bytes memory code =
            hex"60425f5260205f5f5f6001732000000000000000000000000000000000000002620f4240f26020523d60405260605ff3";
        bytes memory accountCode = hex"602a5f5260205ff3";
        runCaseWithBalanceAndAccountCode(
            "callcode-value-insufficient-balance-keeps-output-clears-returndata", code, 0, WORKER, accountCode
        );
    }

    function testCallValueInvalidKeepsOutputAndClearsReturndataParity() public {
        bytes memory code =
            hex"60425f5260205f5f5f6001732000000000000000000000000000000000000002620f4240f16020523d60405260605ff3";
        bytes memory accountCode = hex"fe";
        runCaseWithBalanceAndAccountCode(
            "call-value-invalid-keeps-output-clears-returndata", code, 5, WORKER, accountCode
        );
    }

    function testCallValueMemoryOogKeepsOutputAndClearsReturndataParity() public {
        bytes memory code =
            hex"60425f5260205f5f5f6001732000000000000000000000000000000000000002620f4240f16020523d60405260605ff3";
        bytes memory accountCode = hex"600162ffffff52";
        runCaseWithBalanceAndAccountCode(
            "call-value-memory-oog-keeps-output-clears-returndata", code, 5, WORKER, accountCode
        );
    }

    function testStaticcallInvalidKeepsOutputAndClearsReturndataParity() public {
        bytes memory code =
            hex"60425f5260205f5f5f732000000000000000000000000000000000000002620f4240fa6020523d60405260605ff3";
        bytes memory accountCode = hex"fe";
        runCaseWithBalanceAndAccountCode(
            "staticcall-invalid-keeps-output-clears-returndata", code, 0, WORKER, accountCode
        );
    }

    function testStaticcallMemoryOogKeepsOutputAndClearsReturndataParity() public {
        bytes memory code =
            hex"60425f5260205f5f5f732000000000000000000000000000000000000002620f4240fa6020523d60405260605ff3";
        bytes memory accountCode = hex"600162ffffff52";
        runCaseWithBalanceAndAccountCode(
            "staticcall-memory-oog-keeps-output-clears-returndata", code, 0, WORKER, accountCode
        );
    }

    function testCallcodeInvalidKeepsOutputAndClearsReturndataParity() public {
        bytes memory code =
            hex"60425f5260205f5f5f5f732000000000000000000000000000000000000002620f4240f26020523d60405260605ff3";
        bytes memory accountCode = hex"fe";
        runCaseWithBalanceAndAccountCode(
            "callcode-invalid-keeps-output-clears-returndata", code, 0, WORKER, accountCode
        );
    }

    function testCallcodeMemoryOogKeepsOutputAndClearsReturndataParity() public {
        bytes memory code =
            hex"60425f5260205f5f5f5f732000000000000000000000000000000000000002620f4240f26020523d60405260605ff3";
        bytes memory accountCode = hex"600162ffffff52";
        runCaseWithBalanceAndAccountCode(
            "callcode-memory-oog-keeps-output-clears-returndata", code, 0, WORKER, accountCode
        );
    }

    function testDelegatecallInvalidKeepsOutputAndClearsReturndataParity() public {
        bytes memory code =
            hex"60425f5260205f5f5f732000000000000000000000000000000000000002620f4240f46020523d60405260605ff3";
        bytes memory accountCode = hex"fe";
        runCaseWithBalanceAndAccountCode(
            "delegatecall-invalid-keeps-output-clears-returndata", code, 0, WORKER, accountCode
        );
    }

    function testDelegatecallMemoryOogKeepsOutputAndClearsReturndataParity() public {
        bytes memory code =
            hex"60425f5260205f5f5f732000000000000000000000000000000000000002620f4240f46020523d60405260605ff3";
        bytes memory accountCode = hex"600162ffffff52";
        runCaseWithBalanceAndAccountCode(
            "delegatecall-memory-oog-keeps-output-clears-returndata", code, 0, WORKER, accountCode
        );
    }

    function testCallValueInsufficientBalanceWarmsTargetParity() public {
        bytes memory code =
            hex"5f5f5f5f6001734000000000000000000000000000000000000004620f4240f15f527340000000000000000000000000000000000000043f60205260405ff3";
        runCaseWithBalance("call-value-insufficient-balance-warms-target", code, 0);
    }

    function testCallSelfValueSufficientBalanceParity() public {
        bytes memory code = hex"366017575f5f60015f600130620f4240f15f5260205ff35b00";
        runCaseWithBalance("call-self-value-sufficient-balance", code, 2);
    }

    function testRootRevertRollsBackCallvalueBalanceParity() public {
        bytes memory code = hex"5f5ffd";
        runCaseWithBalanceValueAndAccountCode("root-revert-rolls-back-callvalue-balance", code, 5, 3, address(0), hex"");
    }

    function testRootInvalidOpcodeRollsBackCallvalueBalanceParity() public {
        bytes memory code = hex"fe";
        runCaseWithBalanceValueAndAccountCodeSkippingGas(
            "root-invalid-opcode-rolls-back-callvalue-balance", code, 5, 3, address(0), hex""
        );
    }

    function testRootMemoryOogRollsBackCallvalueBalanceParity() public {
        bytes memory code = hex"600162ffffff52";
        runCaseWithBalanceValueAndAccountCodeSkippingGas(
            "root-memory-oog-rolls-back-callvalue-balance", code, 5, 3, address(0), hex""
        );
    }

    function testCallValueToReturningAccountCommitsBalanceParity() public {
        bytes memory code =
            hex"5f5f5f5f6003732000000000000000000000000000000000000002620f4240f15f52732000000000000000000000000000000000000002316020524760405260605ff3";
        bytes memory accountCode = hex"00";
        runCaseWithBalanceAndAccountCode("call-value-returning-account-commits-balance", code, 5, WORKER, accountCode);
    }

    function testCallValueToRevertingAccountRollsBackBalanceParity() public {
        bytes memory code =
            hex"5f5f5f5f6003732000000000000000000000000000000000000002620f4240f15f52732000000000000000000000000000000000000002316020524760405260605ff3";
        bytes memory accountCode = hex"5f5ffd";
        runCaseWithBalanceAndAccountCode(
            "call-value-reverting-account-rolls-back-balance", code, 5, WORKER, accountCode
        );
    }

    function testCallValueToInvalidAccountRollsBackBalanceParity() public {
        bytes memory code =
            hex"5f5f5f5f6003732000000000000000000000000000000000000002620f4240f15f52732000000000000000000000000000000000000002316020524760405260605ff3";
        bytes memory accountCode = hex"fe";
        runCaseWithBalanceAndAccountCode("call-value-invalid-account-rolls-back-balance", code, 5, WORKER, accountCode);
    }

    function testCallValueToMemoryOogAccountRollsBackBalanceParity() public {
        bytes memory code =
            hex"5f5f5f5f6003732000000000000000000000000000000000000002620f4240f15f52732000000000000000000000000000000000000002316020524760405260605ff3";
        bytes memory accountCode = hex"600162ffffff52";
        runCaseWithBalanceAndAccountCode(
            "call-value-memory-oog-account-rolls-back-balance", code, 5, WORKER, accountCode
        );
    }

    function testParentRevertRollsBackSuccessfulChildValueCallParity() public {
        bytes memory code = hex"5f5f5f5f6003732000000000000000000000000000000000000002620f4240f15f5ffd";
        bytes memory accountCode = hex"00";
        runCaseWithBalanceAndAccountCode("parent-revert-rolls-back-child-value-call", code, 5, WORKER, accountCode);
    }

    function testParentInvalidRollsBackSuccessfulChildValueCallParity() public {
        bytes memory code = hex"5f5f5f5f6003732000000000000000000000000000000000000002620f4240f1fe";
        bytes memory accountCode = hex"00";
        runCaseWithBalanceValueAndAccountCodeSkippingGas(
            "parent-invalid-rolls-back-child-value-call", code, 5, 0, WORKER, accountCode
        );
    }

    function testParentMemoryOogRollsBackSuccessfulChildValueCallParity() public {
        bytes memory code = hex"5f5f5f5f6003732000000000000000000000000000000000000002620f4240f1600162ffffff52";
        bytes memory accountCode = hex"00";
        runCaseWithBalanceValueAndAccountCodeSkippingGas(
            "parent-memory-oog-rolls-back-child-value-call", code, 5, 0, WORKER, accountCode
        );
    }

    function testCallcodeValueExecutesCodeInCallerContextParity() public {
        bytes memory code = hex"60605f5f5f6001732000000000000000000000000000000000000002620f4240f260605260805ff3";
        bytes memory accountCode = hex"345f52306020523360405260605ff3";
        runCaseWithBalanceAndAccountCode("callcode-value-code-caller-context", code, 2, WORKER, accountCode);
    }

    function testDelegatecallValueExecutesCodeInCallerContextParity() public {
        bytes memory code = hex"60605f5f5f732000000000000000000000000000000000000002620f4240f460605260805ff3";
        bytes memory accountCode = hex"345f52306020523360405260605ff3";
        runCaseWithBalanceValueAndAccountCode("delegatecall-value-code-caller-context", code, 0, 7, WORKER, accountCode);
    }

    function testCallcodeSuccessCommitsCallerStorageParity() public {
        bytes memory code = hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f25f525f5460205260405ff3";
        bytes memory accountCode = hex"60015f5500";
        runCaseWithBalanceAndAccountCode("callcode-success-commits-caller-storage", code, 0, WORKER, accountCode);
    }

    function testCallcodeRevertRollsBackCallerStorageParity() public {
        bytes memory code = hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f25f525f5460205260405ff3";
        bytes memory accountCode = hex"60015f555f5ffd";
        runCaseWithBalanceAndAccountCode("callcode-revert-rolls-back-caller-storage", code, 0, WORKER, accountCode);
    }

    function testCallcodeInvalidRollsBackCallerStorageParity() public {
        bytes memory code = hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f25f525f5460205260405ff3";
        bytes memory accountCode = hex"60015f55fe";
        runCaseWithBalanceAndAccountCode("callcode-invalid-rolls-back-caller-storage", code, 0, WORKER, accountCode);
    }

    function testCallcodeMemoryOogRollsBackCallerStorageParity() public {
        bytes memory code = hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f25f525f5460205260405ff3";
        bytes memory accountCode = hex"60015f55600162ffffff52";
        runCaseWithBalanceAndAccountCode("callcode-memory-oog-rolls-back-caller-storage", code, 0, WORKER, accountCode);
    }

    function testDelegatecallSuccessCommitsCallerStorageParity() public {
        bytes memory code = hex"5f5f5f5f732000000000000000000000000000000000000002620f4240f45f525f5460205260405ff3";
        bytes memory accountCode = hex"60015f5500";
        runCaseWithBalanceAndAccountCode("delegatecall-success-commits-caller-storage", code, 0, WORKER, accountCode);
    }

    function testDelegatecallRevertRollsBackCallerStorageParity() public {
        bytes memory code = hex"5f5f5f5f732000000000000000000000000000000000000002620f4240f45f525f5460205260405ff3";
        bytes memory accountCode = hex"60015f555f5ffd";
        runCaseWithBalanceAndAccountCode("delegatecall-revert-rolls-back-caller-storage", code, 0, WORKER, accountCode);
    }

    function testDelegatecallInvalidRollsBackCallerStorageParity() public {
        bytes memory code = hex"5f5f5f5f732000000000000000000000000000000000000002620f4240f45f525f5460205260405ff3";
        bytes memory accountCode = hex"60015f55fe";
        runCaseWithBalanceAndAccountCode("delegatecall-invalid-rolls-back-caller-storage", code, 0, WORKER, accountCode);
    }

    function testDelegatecallMemoryOogRollsBackCallerStorageParity() public {
        bytes memory code = hex"5f5f5f5f732000000000000000000000000000000000000002620f4240f45f525f5460205260405ff3";
        bytes memory accountCode = hex"60015f55600162ffffff52";
        runCaseWithBalanceAndAccountCode(
            "delegatecall-memory-oog-rolls-back-caller-storage", code, 0, WORKER, accountCode
        );
    }

    function testParentInvalidRollsBackSuccessfulChildStorageWriteParity() public {
        bytes memory code = hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f1fe";
        bytes memory accountCode = hex"60015f5500";
        runParentChildStorageCaseWithGasMode(
            "parent-invalid-rolls-back-child-storage-write", code, WORKER, accountCode, true
        );
    }

    function testParentMemoryOogRollsBackSuccessfulChildStorageWriteParity() public {
        bytes memory code = hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f1600162ffffff52";
        bytes memory accountCode = hex"60015f5500";
        runParentChildStorageCaseWithGasMode(
            "parent-memory-oog-rolls-back-child-storage-write", code, WORKER, accountCode, true
        );
    }

    function testEip7702DelegatedCallExecutesTargetCodeParity() public {
        bytes memory code = hex"60205f5f5f5f732000000000000000000000000000000000000002620f4240f160205260405ff3";
        bytes memory designatorCode = hex"ef01003000000000000000000000000000000000000003";
        bytes memory delegatedCode = hex"305f5260205ff3";
        runCaseWithBalanceValueAndTwoAccountCodes(
            "eip7702-delegated-call-executes-target-code",
            code,
            0,
            0,
            WORKER,
            designatorCode,
            DELEGATE_LIB,
            delegatedCode
        );
    }

    function testEip7702DelegatedCallcodeExecutesTargetCodeParity() public {
        bytes memory code = hex"60605f5f5f5f732000000000000000000000000000000000000002620f4240f260605260805ff3";
        bytes memory designatorCode = hex"ef01003000000000000000000000000000000000000003";
        bytes memory delegatedCode = hex"305f52336020523460405260605ff3";
        runCaseWithBalanceValueAndTwoAccountCodes(
            "eip7702-delegated-callcode-executes-target-code",
            code,
            0,
            0,
            WORKER,
            designatorCode,
            DELEGATE_LIB,
            delegatedCode
        );
    }

    function testEip7702DelegatedDelegatecallExecutesTargetCodeParity() public {
        bytes memory code = hex"60605f5f5f732000000000000000000000000000000000000002620f4240f460605260805ff3";
        bytes memory designatorCode = hex"ef01003000000000000000000000000000000000000003";
        bytes memory delegatedCode = hex"305f52336020523460405260605ff3";
        runCaseWithBalanceValueAndTwoAccountCodes(
            "eip7702-delegated-delegatecall-executes-target-code",
            code,
            0,
            7,
            WORKER,
            designatorCode,
            DELEGATE_LIB,
            delegatedCode
        );
    }

    function testEip7702DelegatedStaticcallExecutesTargetCodeParity() public {
        bytes memory code = hex"60205f5f5f732000000000000000000000000000000000000002620f4240fa60205260405ff3";
        bytes memory designatorCode = hex"ef01003000000000000000000000000000000000000003";
        bytes memory delegatedCode = hex"305f5260205ff3";
        runCaseWithBalanceValueAndTwoAccountCodes(
            "eip7702-delegated-staticcall-executes-target-code",
            code,
            0,
            0,
            WORKER,
            designatorCode,
            DELEGATE_LIB,
            delegatedCode
        );
    }

    function testEip7702DelegatedCallUsesAuthorityStorageParity() public {
        bytes memory code =
            hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f15f526020602060015f5f732000000000000000000000000000000000000002620f4240f160405260605ff3";
        bytes memory designatorCode = hex"ef01003000000000000000000000000000000000000003";
        bytes memory delegatedCode = hex"3660095760015f55005b5f545f5260205ff3";
        runCaseWithBalanceValueAndTwoAccountCodes(
            "eip7702-delegated-call-uses-authority-storage",
            code,
            0,
            0,
            WORKER,
            designatorCode,
            DELEGATE_LIB,
            delegatedCode
        );
    }

    function testEip7702DelegatedCallcodeUsesCallerStorageParity() public {
        bytes memory code = hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f25f525f5460205260405ff3";
        bytes memory designatorCode = hex"ef01003000000000000000000000000000000000000003";
        bytes memory delegatedCode = hex"60015f5500";
        runCaseWithBalanceValueAndTwoAccountCodes(
            "eip7702-delegated-callcode-uses-caller-storage",
            code,
            0,
            0,
            WORKER,
            designatorCode,
            DELEGATE_LIB,
            delegatedCode
        );
    }

    function testEip7702DelegatedDelegatecallUsesCallerStorageParity() public {
        bytes memory code = hex"5f5f5f5f732000000000000000000000000000000000000002620f4240f45f525f5460205260405ff3";
        bytes memory designatorCode = hex"ef01003000000000000000000000000000000000000003";
        bytes memory delegatedCode = hex"60015f5500";
        runCaseWithBalanceValueAndTwoAccountCodes(
            "eip7702-delegated-delegatecall-uses-caller-storage",
            code,
            0,
            0,
            WORKER,
            designatorCode,
            DELEGATE_LIB,
            delegatedCode
        );
    }

    function testEip7702DelegatedStaticcallRejectsStorageWriteParity() public {
        bytes memory code =
            hex"5f5f5f5f732000000000000000000000000000000000000002620f4240fa5f526020602060015f5f732000000000000000000000000000000000000002620f4240f160405260605ff3";
        bytes memory designatorCode = hex"ef01003000000000000000000000000000000000000003";
        bytes memory delegatedCode = hex"3660095760015f55005b5f545f5260205ff3";
        runCaseWithBalanceValueAndTwoAccountCodes(
            "eip7702-delegated-staticcall-rejects-storage-write",
            code,
            0,
            0,
            WORKER,
            designatorCode,
            DELEGATE_LIB,
            delegatedCode
        );
    }

    function testEip7702DelegationStopsAfterOneHopParity() public {
        bytes memory code = hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f15f5260205ff3";
        bytes memory designatorCode = hex"ef01003000000000000000000000000000000000000003";
        bytes memory secondHopDesignatorCode = hex"ef01000000000000000000000000000000000000000004";
        runCaseWithBalanceValueAndTwoAccountCodes(
            "eip7702-delegation-stops-after-one-hop",
            code,
            0,
            0,
            WORKER,
            designatorCode,
            DELEGATE_LIB,
            secondHopDesignatorCode
        );
    }

    function testEip7702DelegatedCodesizeKeepsAuthorityExtcodesizeParity() public {
        bytes memory code = hex"60405f5f5f5f732000000000000000000000000000000000000002620f4240f160405260605ff3";
        bytes memory designatorCode = hex"ef01003000000000000000000000000000000000000003";
        bytes memory delegatedCode = hex"385f52303b60205260405ff3";
        runCaseWithBalanceValueAndTwoAccountCodes(
            "eip7702-delegated-codesize-authority-extcodesize",
            code,
            0,
            0,
            WORKER,
            designatorCode,
            DELEGATE_LIB,
            delegatedCode
        );
    }

    function testEip7702DelegationToPrecompileExecutesEmptyCodeParity() public {
        bytes memory code =
            hex"60425f526020604060205f5f732000000000000000000000000000000000000002620f4240f16060523d60805260a05ff3";
        bytes memory designatorCode = hex"ef01000000000000000000000000000000000000000004";
        runCaseWithBalanceAndAccountCode(
            "eip7702-delegation-to-precompile-executes-empty-code", code, 0, WORKER, designatorCode
        );
    }

    function testStaticcallAllowsCallcodeValueParity() public {
        bytes memory code = hex"5f5f5f5f732000000000000000000000000000000000000002620f4240fa5f5260205ff3";
        bytes memory accountCode = hex"5f5f5f5f6001734000000000000000000000000000000000000004620f4240f200";
        runCaseWithBalanceAndAccountCode("staticcall-allows-callcode-value", code, 0, WORKER, accountCode);
    }

    function testStaticcallRejectsCallValueParity() public {
        bytes memory code = hex"5f5f5f5f732000000000000000000000000000000000000002620f4240fa5f5260205ff3";
        bytes memory accountCode = hex"5f5f5f5f6001734000000000000000000000000000000000000004620f4240f100";
        runCaseWithBalanceAndAccountCode("staticcall-rejects-call-value", code, 0, WORKER, accountCode);
    }

    function testStaticcallOutputTruncationReturndataParity() public {
        bytes memory code =
            hex"60045f5f5f732000000000000000000000000000000000000002620f4240fa6040523d6020523d5f60603e60805ff3";
        bytes memory accountCode = hex"7f0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f205f5260205ff3";
        runCaseWithBalanceAndAccountCode("staticcall-output-truncation-returndata", code, 0, WORKER, accountCode);
    }

    function testStaticcallShortReturndataKeepsOutputTailParity() public {
        bytes memory code =
            hex"7f42424242424242424242424242424242424242424242424242424242424242425f5260205f5f5f732000000000000000000000000000000000000002620f4240fa6020523d60405260605ff3";
        bytes memory accountCode = hex"60ab5f5360015ff3";
        runCaseWithBalanceAndAccountCode("staticcall-short-returndata-keeps-output-tail", code, 0, WORKER, accountCode);
    }

    function testStaticcallRevertReturndataParity() public {
        bytes memory code =
            hex"5f5f5f5f732000000000000000000000000000000000000002620f4240fa6040523d5f5260205f60203e60605ff3";
        bytes memory accountCode = hex"602a5f5260205ffd";
        runCaseWithBalanceAndAccountCode("staticcall-revert-returndata", code, 0, WORKER, accountCode);
    }

    function testCallShortReturndataKeepsOutputTailParity() public {
        bytes memory code =
            hex"7f42424242424242424242424242424242424242424242424242424242424242425f5260205f5f5f5f732000000000000000000000000000000000000002620f4240f16020523d60405260605ff3";
        bytes memory accountCode = hex"60ab5f5360015ff3";
        runCaseWithBalanceAndAccountCode("call-short-returndata-keeps-output-tail", code, 0, WORKER, accountCode);
    }

    function testCallRevertReturndataParity() public {
        bytes memory code =
            hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f16040523d5f5260205f60203e60605ff3";
        bytes memory accountCode = hex"602a5f5260205ffd";
        runCaseWithBalanceAndAccountCode("call-revert-returndata", code, 0, WORKER, accountCode);
    }

    function testCallcodeOutputTruncationReturndataParity() public {
        bytes memory code =
            hex"60045f5f5f5f732000000000000000000000000000000000000002620f4240f26040523d6020523d5f60603e60805ff3";
        bytes memory accountCode = hex"7f0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f205f5260205ff3";
        runCaseWithBalanceAndAccountCode("callcode-output-truncation-returndata", code, 0, WORKER, accountCode);
    }

    function testDelegatecallOutputTruncationReturndataParity() public {
        bytes memory code =
            hex"60045f5f5f732000000000000000000000000000000000000002620f4240f46040523d6020523d5f60603e60805ff3";
        bytes memory accountCode = hex"7f0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f205f5260205ff3";
        runCaseWithBalanceAndAccountCode("delegatecall-output-truncation-returndata", code, 0, WORKER, accountCode);
    }

    function testCallcodeShortReturndataKeepsOutputTailParity() public {
        bytes memory code =
            hex"7f42424242424242424242424242424242424242424242424242424242424242425f5260205f5f5f5f732000000000000000000000000000000000000002620f4240f26020523d60405260605ff3";
        bytes memory accountCode = hex"60ab5f5360015ff3";
        runCaseWithBalanceAndAccountCode("callcode-short-returndata-keeps-output-tail", code, 0, WORKER, accountCode);
    }

    function testDelegatecallShortReturndataKeepsOutputTailParity() public {
        bytes memory code =
            hex"7f42424242424242424242424242424242424242424242424242424242424242425f5260205f5f5f732000000000000000000000000000000000000002620f4240f46020523d60405260605ff3";
        bytes memory accountCode = hex"60ab5f5360015ff3";
        runCaseWithBalanceAndAccountCode(
            "delegatecall-short-returndata-keeps-output-tail", code, 0, WORKER, accountCode
        );
    }

    function testCallcodeRevertReturndataParity() public {
        bytes memory code =
            hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f26040523d5f5260205f60203e60605ff3";
        bytes memory accountCode = hex"602a5f5260205ffd";
        runCaseWithBalanceAndAccountCode("callcode-revert-returndata", code, 0, WORKER, accountCode);
    }

    function testDelegatecallRevertReturndataParity() public {
        bytes memory code =
            hex"5f5f5f5f732000000000000000000000000000000000000002620f4240f46040523d5f5260205f60203e60605ff3";
        bytes memory accountCode = hex"602a5f5260205ffd";
        runCaseWithBalanceAndAccountCode("delegatecall-revert-returndata", code, 0, WORKER, accountCode);
    }

    function testStaticcallPropagatesIntoCallcodeParity() public {
        bytes memory code = hex"60205f5f5f732000000000000000000000000000000000000002620f4240fa60205ff3";
        bytes memory workerCode = hex"5f5f5f5f5f733000000000000000000000000000000000000003620f4240f25f5260205ff3";
        bytes memory libraryCode = hex"600160005500";
        runCaseWithBalanceValueAndTwoAccountCodes(
            "staticcall-propagates-into-callcode", code, 0, 0, WORKER, workerCode, DELEGATE_LIB, libraryCode
        );
    }

    function testStaticcallPropagatesIntoCallParity() public {
        bytes memory code = hex"60205f5f5f732000000000000000000000000000000000000002620f4240fa60205ff3";
        bytes memory workerCode = hex"5f5f5f5f5f733000000000000000000000000000000000000003620f4240f15f5260205ff3";
        bytes memory libraryCode = hex"600160005500";
        runCaseWithBalanceValueAndTwoAccountCodes(
            "staticcall-propagates-into-call", code, 0, 0, WORKER, workerCode, DELEGATE_LIB, libraryCode
        );
    }

    function testStaticcallPropagatesIntoCallLogParity() public {
        bytes memory code = hex"60205f5f5f732000000000000000000000000000000000000002620f4240fa60205ff3";
        bytes memory workerCode = hex"5f5f5f5f5f733000000000000000000000000000000000000003620f4240f15f5260205ff3";
        bytes memory libraryCode = hex"60425f5fa100";
        runCaseWithBalanceValueAndTwoAccountCodes(
            "staticcall-propagates-into-call-log", code, 0, 0, WORKER, workerCode, DELEGATE_LIB, libraryCode
        );
    }

    function testStaticcallPropagatesIntoDelegatecallParity() public {
        bytes memory code = hex"60205f5f5f732000000000000000000000000000000000000002620f4240fa60205ff3";
        bytes memory workerCode = hex"5f5f5f5f733000000000000000000000000000000000000003620f4240f45f5260205ff3";
        bytes memory libraryCode = hex"600160005500";
        runCaseWithBalanceValueAndTwoAccountCodes(
            "staticcall-propagates-into-delegatecall", code, 0, 0, WORKER, workerCode, DELEGATE_LIB, libraryCode
        );
    }

    function testStaticcallRejectsCreateParity() public {
        bytes memory code = hex"60205f5f5f732000000000000000000000000000000000000002620f4240fa60205ff3";
        bytes memory workerCode = hex"5f5f5ff05f5260205ff3";
        runCaseWithBalanceAndAccountCode("staticcall-rejects-create", code, 0, WORKER, workerCode);
    }

    function testStaticcallRejectsCreate2Parity() public {
        bytes memory code = hex"60205f5f5f732000000000000000000000000000000000000002620f4240fa60205ff3";
        bytes memory workerCode = hex"5f5f5f5ff55f5260205ff3";
        runCaseWithBalanceAndAccountCode("staticcall-rejects-create2", code, 0, WORKER, workerCode);
    }

    function testSelfdestructZeroBalanceToMissingAccountDoesNotMaterializeParity() public {
        bytes memory code =
            hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f1507340000000000000000000000000000000000000043f5f5260205ff3";
        bytes memory accountCode = hex"734000000000000000000000000000000000000004ff";
        runCaseWithBalanceAndAccountCode(
            "selfdestruct-zero-balance-missing-not-materialized", code, 0, WORKER, accountCode
        );
    }

    function testPreexistingSelfdestructAccountRemainsCallableParity() public {
        bytes memory code =
            hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f15060015f5360205f60015f5f732000000000000000000000000000000000000002620f4240f160205260405ff3";
        bytes memory accountCode = hex"3615600d57602a5f5260205ff35b733000000000000000000000000000000000000003ff";
        runCaseWithBalanceAndAccountCode(
            "preexisting-selfdestruct-account-remains-callable", code, 0, WORKER, accountCode
        );
    }

    function testPreexistingSelfdestructSecondCallCannotDoubleTransferParity() public {
        bytes memory code =
            hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f15f5f5f5f5f732000000000000000000000000000000000000002620f4240f100";
        bytes memory accountCode = hex"733000000000000000000000000000000000000003ff";
        runParentRevertChildSelfdestructBalanceCase(
            "preexisting-selfdestruct-second-call-cannot-double-transfer", code, WORKER, accountCode, 7, DELEGATE_LIB
        );
    }

    function testChildSelfdestructToPrecompileTransfersBalanceParity() public {
        bytes memory code = hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f100";
        bytes memory accountCode = hex"6004ff";
        runParentRevertChildSelfdestructBalanceCase(
            "child-selfdestruct-to-precompile-transfers-balance", code, WORKER, accountCode, 7, address(4)
        );
    }

    function testParentRevertRollsBackSuccessfulChildSelfdestructParity() public {
        bytes memory code = hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f15f5ffd";
        bytes memory accountCode = hex"733000000000000000000000000000000000000003ff";
        runCaseWithBalanceAndAccountCode("parent-revert-rolls-back-child-selfdestruct", code, 0, WORKER, accountCode);
    }

    function testParentInvalidRollsBackSuccessfulChildSelfdestructParity() public {
        bytes memory code = hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f1fe";
        bytes memory accountCode = hex"733000000000000000000000000000000000000003ff";
        runCaseWithBalanceValueAndAccountCodeSkippingGas(
            "parent-invalid-rolls-back-child-selfdestruct", code, 0, 0, WORKER, accountCode
        );
    }

    function testParentMemoryOogRollsBackSuccessfulChildSelfdestructParity() public {
        bytes memory code = hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f1600162ffffff52";
        bytes memory accountCode = hex"733000000000000000000000000000000000000003ff";
        runCaseWithBalanceValueAndAccountCodeSkippingGas(
            "parent-memory-oog-rolls-back-child-selfdestruct", code, 0, 0, WORKER, accountCode
        );
    }

    function testParentRevertRollsBackChildSelfdestructBalanceTransferParity() public {
        bytes memory code = hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f15f5ffd";
        bytes memory accountCode = hex"733000000000000000000000000000000000000003ff";
        runParentRevertChildSelfdestructBalanceCase(
            "parent-revert-rolls-back-child-selfdestruct-balance", code, WORKER, accountCode, 7, DELEGATE_LIB
        );
    }

    function testParentInvalidRollsBackChildSelfdestructBalanceTransferParity() public {
        bytes memory code = hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f1fe";
        bytes memory accountCode = hex"733000000000000000000000000000000000000003ff";
        runParentChildSelfdestructBalanceCaseWithGasMode(
            "parent-invalid-rolls-back-child-selfdestruct-balance", code, WORKER, accountCode, 7, DELEGATE_LIB, true
        );
    }

    function testParentMemoryOogRollsBackChildSelfdestructBalanceTransferParity() public {
        bytes memory code = hex"5f5f5f5f5f732000000000000000000000000000000000000002620f4240f1600162ffffff52";
        bytes memory accountCode = hex"733000000000000000000000000000000000000003ff";
        runParentChildSelfdestructBalanceCaseWithGasMode(
            "parent-memory-oog-rolls-back-child-selfdestruct-balance", code, WORKER, accountCode, 7, DELEGATE_LIB, true
        );
    }

    function runCase(string memory name, bytes memory code) internal {
        runCaseWithBalance(name, code, 0);
    }

    function runCaseWithBalance(string memory name, bytes memory code, uint256 initialBalance) internal {
        runCaseWithBalanceAndAccountCode(name, code, initialBalance, address(0), hex"");
    }

    function runCaseWithBalanceAndAccountCode(
        string memory name,
        bytes memory code,
        uint256 initialBalance,
        address account,
        bytes memory accountCode
    ) internal {
        runCaseWithBalanceValueAndAccountCode(name, code, initialBalance, 0, account, accountCode);
    }

    function runCaseWithBalanceValueAndAccountCode(
        string memory name,
        bytes memory code,
        uint256 initialBalance,
        uint256 callValue,
        address account,
        bytes memory accountCode
    ) internal {
        runCaseWithBalanceValueAndTwoAccountCodes(
            name, code, initialBalance, callValue, account, accountCode, address(0), hex""
        );
    }

    function runCaseWithBalanceValueAndAccountCodeSkippingGas(
        string memory name,
        bytes memory code,
        uint256 initialBalance,
        uint256 callValue,
        address account,
        bytes memory accountCode
    ) internal {
        runCaseWithBalanceValueAndTwoAccountCodesWithGasMode(
            name, code, initialBalance, callValue, account, accountCode, address(0), hex"", true
        );
    }

    function runCaseWithBalanceValueAndTwoAccountCodes(
        string memory name,
        bytes memory code,
        uint256 initialBalance,
        uint256 callValue,
        address firstAccount,
        bytes memory firstAccountCode,
        address secondAccount,
        bytes memory secondAccountCode
    ) internal {
        runCaseWithBalanceValueAndTwoAccountCodesWithGasMode(
            name,
            code,
            initialBalance,
            callValue,
            firstAccount,
            firstAccountCode,
            secondAccount,
            secondAccountCode,
            false
        );
    }

    function runCaseWithBalanceValueAndTwoAccountCodesWithGasMode(
        string memory name,
        bytes memory code,
        uint256 initialBalance,
        uint256 callValue,
        address firstAccount,
        bytes memory firstAccountCode,
        address secondAccount,
        bytes memory secondAccountCode,
        bool skipGas
    ) internal {
        address target = installRuntime(code);
        vm.deal(target, initialBalance);
        if (callValue != 0) {
            vm.deal(address(this), callValue);
        }
        bool hasFirstAccountCode = firstAccount != address(0);
        bool hasSecondAccountCode = secondAccount != address(0);
        if (hasFirstAccountCode) {
            vm.etch(firstAccount, firstAccountCode);
        }
        if (hasSecondAccountCode) {
            vm.etch(secondAccount, secondAccountCode);
        }

        (bool success, bytes memory output) = target.call{gas: GAS_LIMIT, value: callValue}(hex"");
        CallAccountVm.Gas memory gas = vm.lastCallGas();

        string[] memory command =
            new string[](43 + (skipGas ? 1 : 0) + (hasFirstAccountCode ? 8 : 0) + (hasSecondAccountCode ? 8 : 0));
        command[0] = "python3";
        command[1] = "../../bin/evm_parity.py";
        command[2] = "check";
        command[3] = "--case";
        command[4] = name;
        command[5] = "--code";
        command[6] = hexString(code);
        command[7] = "--calldata";
        command[8] = "0x";
        command[9] = "--gas";
        command[10] = uintToString(gas.gasLimit);
        command[11] = "--success";
        command[12] = success ? "1" : "0";
        command[13] = "--output";
        command[14] = hexString(output);
        command[15] = "--gas-used";
        command[16] = uintToString(gas.gasTotalUsed);
        command[17] = "--gas-remaining";
        command[18] = uintToString(gas.gasRemaining);
        command[19] = "--gas-refunded";
        command[20] = intToString(gas.gasRefunded);
        command[21] = "--caller";
        command[22] = addressArg(address(this));
        command[23] = "--origin";
        command[24] = addressArg(tx.origin);
        command[25] = "--callvalue";
        command[26] = uintToString(callValue);
        command[27] = "--balance";
        command[28] = uintToString(initialBalance + callValue);
        command[29] = "--expect-balance";
        command[30] = uintToString(target.balance);
        command[31] = "--coinbase";
        command[32] = addressArg(block.coinbase);
        command[33] = "--timestamp";
        command[34] = uintToString(block.timestamp);
        command[35] = "--number";
        command[36] = uintToString(block.number);
        command[37] = "--block-gas-limit";
        command[38] = uintToString(block.gaslimit);
        command[39] = "--basefee";
        command[40] = uintToString(block.basefee);
        command[41] = "--chainid";
        command[42] = uintToString(block.chainid);

        uint256 cursor = 43;
        if (skipGas) {
            command[cursor++] = "--skip-gas";
        }
        if (hasFirstAccountCode) {
            command[cursor++] = "--account";
            command[cursor++] = string.concat(addressArg(firstAccount), "=", hexString(firstAccountCode));
            command[cursor++] = "--warm-address";
            command[cursor++] = addressArg(firstAccount);
            command[cursor++] = "--expect-account-code";
            command[cursor++] = string.concat(addressArg(firstAccount), "=", hexString(firstAccountCode));
            command[cursor++] = "--expect-account-balance";
            command[cursor++] = string.concat(addressArg(firstAccount), "=", uintToString(firstAccount.balance));
        }
        if (hasSecondAccountCode) {
            command[cursor++] = "--account";
            command[cursor++] = string.concat(addressArg(secondAccount), "=", hexString(secondAccountCode));
            command[cursor++] = "--warm-address";
            command[cursor++] = addressArg(secondAccount);
            command[cursor++] = "--expect-account-code";
            command[cursor++] = string.concat(addressArg(secondAccount), "=", hexString(secondAccountCode));
            command[cursor++] = "--expect-account-balance";
            command[cursor++] = string.concat(addressArg(secondAccount), "=", uintToString(secondAccount.balance));
        }

        vm.ffi(command);
    }

    function runParentChildStorageCaseWithGasMode(
        string memory name,
        bytes memory code,
        address account,
        bytes memory accountCode,
        bool skipGas
    ) internal {
        address target = installRuntime(code);
        vm.etch(account, accountCode);

        (bool success, bytes memory output) = target.call{gas: GAS_LIMIT}(hex"");
        CallAccountVm.Gas memory gas = vm.lastCallGas();

        string[] memory command = new string[](53 + (skipGas ? 1 : 0));
        command[0] = "python3";
        command[1] = "../../bin/evm_parity.py";
        command[2] = "check";
        command[3] = "--case";
        command[4] = name;
        command[5] = "--code";
        command[6] = hexString(code);
        command[7] = "--calldata";
        command[8] = "0x";
        command[9] = "--gas";
        command[10] = uintToString(gas.gasLimit);
        command[11] = "--success";
        command[12] = success ? "1" : "0";
        command[13] = "--output";
        command[14] = hexString(output);
        command[15] = "--gas-used";
        command[16] = uintToString(gas.gasTotalUsed);
        command[17] = "--gas-remaining";
        command[18] = uintToString(gas.gasRemaining);
        command[19] = "--gas-refunded";
        command[20] = intToString(gas.gasRefunded);
        command[21] = "--caller";
        command[22] = addressArg(address(this));
        command[23] = "--origin";
        command[24] = addressArg(tx.origin);
        command[25] = "--callvalue";
        command[26] = "0";
        command[27] = "--balance";
        command[28] = "0";
        command[29] = "--expect-balance";
        command[30] = uintToString(target.balance);
        command[31] = "--coinbase";
        command[32] = addressArg(block.coinbase);
        command[33] = "--timestamp";
        command[34] = uintToString(block.timestamp);
        command[35] = "--number";
        command[36] = uintToString(block.number);
        command[37] = "--block-gas-limit";
        command[38] = uintToString(block.gaslimit);
        command[39] = "--basefee";
        command[40] = uintToString(block.basefee);
        command[41] = "--chainid";
        command[42] = uintToString(block.chainid);
        command[43] = "--account";
        command[44] = string.concat(addressArg(account), "=", hexString(accountCode));
        command[45] = "--warm-address";
        command[46] = addressArg(account);
        command[47] = "--expect-account-code";
        command[48] = string.concat(addressArg(account), "=", hexString(accountCode));
        command[49] = "--expect-account-storage";
        command[50] =
            string.concat(addressArg(account), ":", wordHex(bytes32(0)), "=", wordHex(vm.load(account, bytes32(0))));
        command[51] = "--expect-account-balance";
        command[52] = string.concat(addressArg(account), "=", uintToString(account.balance));
        if (skipGas) {
            command[53] = "--skip-gas";
        }

        vm.ffi(command);
    }

    function runParentRevertChildSelfdestructBalanceCase(
        string memory name,
        bytes memory code,
        address account,
        bytes memory accountCode,
        uint256 accountBalance,
        address beneficiary
    ) internal {
        runParentChildSelfdestructBalanceCaseWithGasMode(
            name, code, account, accountCode, accountBalance, beneficiary, false
        );
    }

    function runParentChildSelfdestructBalanceCaseWithGasMode(
        string memory name,
        bytes memory code,
        address account,
        bytes memory accountCode,
        uint256 accountBalance,
        address beneficiary,
        bool skipGas
    ) internal {
        address target = installRuntime(code);
        vm.deal(target, 0);
        vm.etch(account, accountCode);
        vm.deal(account, accountBalance);

        (bool success, bytes memory output) = target.call{gas: GAS_LIMIT}(hex"");
        CallAccountVm.Gas memory gas = vm.lastCallGas();

        string[] memory command = new string[](57 + (skipGas ? 1 : 0));
        command[0] = "python3";
        command[1] = "../../bin/evm_parity.py";
        command[2] = "check";
        command[3] = "--case";
        command[4] = name;
        command[5] = "--code";
        command[6] = hexString(code);
        command[7] = "--calldata";
        command[8] = "0x";
        command[9] = "--gas";
        command[10] = uintToString(gas.gasLimit);
        command[11] = "--success";
        command[12] = success ? "1" : "0";
        command[13] = "--output";
        command[14] = hexString(output);
        command[15] = "--gas-used";
        command[16] = uintToString(gas.gasTotalUsed);
        command[17] = "--gas-remaining";
        command[18] = uintToString(gas.gasRemaining);
        command[19] = "--gas-refunded";
        command[20] = intToString(gas.gasRefunded);
        command[21] = "--caller";
        command[22] = addressArg(address(this));
        command[23] = "--origin";
        command[24] = addressArg(tx.origin);
        command[25] = "--callvalue";
        command[26] = "0";
        command[27] = "--balance";
        command[28] = "0";
        command[29] = "--expect-balance";
        command[30] = uintToString(target.balance);
        command[31] = "--coinbase";
        command[32] = addressArg(block.coinbase);
        command[33] = "--timestamp";
        command[34] = uintToString(block.timestamp);
        command[35] = "--number";
        command[36] = uintToString(block.number);
        command[37] = "--block-gas-limit";
        command[38] = uintToString(block.gaslimit);
        command[39] = "--basefee";
        command[40] = uintToString(block.basefee);
        command[41] = "--chainid";
        command[42] = uintToString(block.chainid);
        command[43] = "--account";
        command[44] = string.concat(addressArg(account), "=", hexString(accountCode));
        command[45] = "--account-balance";
        command[46] = string.concat(addressArg(account), "=", uintToString(accountBalance));
        command[47] = "--warm-address";
        command[48] = addressArg(account);
        command[49] = "--expect-account-code";
        command[50] = string.concat(addressArg(account), "=", hexString(accountCode));
        command[51] = "--expect-account-balance";
        command[52] = string.concat(addressArg(account), "=", uintToString(account.balance));
        command[53] = "--expect-account-balance";
        command[54] = string.concat(addressArg(beneficiary), "=", uintToString(beneficiary.balance));
        command[55] = "--expect-account-code";
        command[56] = string.concat(addressArg(beneficiary), "=", hexString(beneficiary.code));
        if (skipGas) {
            command[57] = "--skip-gas";
        }

        vm.ffi(command);
    }

    function installRuntime(bytes memory code) internal returns (address target) {
        target = TARGET;
        vm.etch(target, code);
        require(target.code.length == code.length, "runtime not installed");
    }

    function hexString(bytes memory data) internal pure returns (string memory) {
        bytes memory alphabet = "0123456789abcdef";
        bytes memory out = new bytes(2 + data.length * 2);
        out[0] = "0";
        out[1] = "x";
        for (uint256 i = 0; i < data.length; i++) {
            out[2 + i * 2] = alphabet[uint8(data[i]) >> 4];
            out[3 + i * 2] = alphabet[uint8(data[i]) & 0x0f];
        }
        return string(out);
    }

    function addressArg(address value) internal pure returns (string memory) {
        return hexString(abi.encodePacked(value));
    }

    function wordHex(bytes32 value) internal pure returns (string memory) {
        return hexString(abi.encodePacked(value));
    }

    function uintToString(uint256 value) internal pure returns (string memory) {
        if (value == 0) return "0";
        uint256 temp = value;
        uint256 digits;
        while (temp != 0) {
            digits++;
            temp /= 10;
        }
        bytes memory buffer = new bytes(digits);
        while (value != 0) {
            digits -= 1;
            buffer[digits] = bytes1(uint8(48 + uint256(value % 10)));
            value /= 10;
        }
        return string(buffer);
    }

    function intToString(int256 value) internal pure returns (string memory) {
        if (value >= 0) return uintToString(uint256(value));
        return string.concat("-", uintToString(uint256(-value)));
    }
}
