// SPDX-License-Identifier: GPL-2.0-or-later
pragma solidity ^0.8.20;

import {
    UniswapTransferHelperEthRecipient,
    UniswapTransferHelperHarness,
    UniswapTransferHelperNoReturnToken,
    UniswapTransferHelperRejectEth,
    UniswapTransferHelperReturnFalseToken,
    UniswapTransferHelperReturnTrueToken
} from "../src/UniswapTransferHelper.sol";

contract UniswapTransferHelperForgeTest {
    function _expectError(string memory actual, string memory expected)
        private
        pure
    {
        require(
            keccak256(bytes(actual)) == keccak256(bytes(expected)),
            "error"
        );
    }

    function testSafeTransferFromAcceptsTrueAndNoReturn() public {
        UniswapTransferHelperHarness helper =
            new UniswapTransferHelperHarness();
        UniswapTransferHelperReturnTrueToken returnsTrue =
            new UniswapTransferHelperReturnTrueToken();
        UniswapTransferHelperNoReturnToken noReturn =
            new UniswapTransferHelperNoReturnToken();

        helper.pull(address(returnsTrue), address(0x1111), address(0x2222), 7);
        require(returnsTrue.lastFrom() == address(0x1111), "true from");
        require(returnsTrue.lastTo() == address(0x2222), "true to");
        require(returnsTrue.lastValue() == 7, "true value");

        helper.pull(address(noReturn), address(0x3333), address(0x4444), 9);
        require(noReturn.lastFrom() == address(0x3333), "empty from");
        require(noReturn.lastTo() == address(0x4444), "empty to");
        require(noReturn.lastValue() == 9, "empty value");
    }

    function testSafeTransferFromRejectsFalseAndFailedCall() public {
        UniswapTransferHelperHarness helper =
            new UniswapTransferHelperHarness();
        UniswapTransferHelperReturnFalseToken returnsFalse =
            new UniswapTransferHelperReturnFalseToken();
        UniswapTransferHelperRejectEth rejects =
            new UniswapTransferHelperRejectEth();

        try helper.pull(address(returnsFalse), address(0x1111), address(0x2222), 7) {
            revert("expected false return");
        } catch Error(string memory reason) {
            _expectError(reason, "STF");
        }

        try helper.pull(address(rejects), address(0x1111), address(0x2222), 7) {
            revert("expected failed call");
        } catch Error(string memory reason) {
            _expectError(reason, "STF");
        }
    }

    function testSafeTransferAndApprove() public {
        UniswapTransferHelperHarness helper =
            new UniswapTransferHelperHarness();
        UniswapTransferHelperReturnTrueToken token =
            new UniswapTransferHelperReturnTrueToken();

        helper.push(address(token), address(0x2222), 13);
        require(token.lastTo() == address(0x2222), "transfer to");
        require(token.lastValue() == 13, "transfer value");

        helper.approve(address(token), address(0x3333), 17);
        require(token.lastSpender() == address(0x3333), "spender");
        require(token.lastValue() == 17, "approve value");
    }

    function testSafeTransferETH() public {
        UniswapTransferHelperHarness helper =
            new UniswapTransferHelperHarness();
        UniswapTransferHelperEthRecipient recipient =
            new UniswapTransferHelperEthRecipient();
        UniswapTransferHelperRejectEth rejecter =
            new UniswapTransferHelperRejectEth();

        helper.pay{value: 5}(payable(address(recipient)), 5);
        require(recipient.received() == 5, "received");

        try helper.pay{value: 1}(payable(address(rejecter)), 1) {
            revert("expected eth transfer failure");
        } catch Error(string memory reason) {
            _expectError(reason, "STE");
        }
    }
}
