// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {
    OpenZeppelinERC20Forwarder,
    OpenZeppelinIERC20Errors,
    OpenZeppelinERC20HarnessToken
} from "../src/OpenZeppelinERC20.sol";

contract OpenZeppelinERC20ForgeTest {
    function _expectCustom(bytes memory actual, bytes memory expected)
        private
        pure
    {
        require(keccak256(actual) == keccak256(expected), "custom error");
    }

    function testConstructorMetadataAndInitialMint() public {
        OpenZeppelinERC20HarnessToken token =
            new OpenZeppelinERC20HarnessToken("Harness Token", "HARN", address(this), 100);

        require(
            keccak256(bytes(token.name())) == keccak256(bytes("Harness Token")),
            "name"
        );
        require(keccak256(bytes(token.symbol())) == keccak256(bytes("HARN")), "symbol");
        require(token.decimals() == 18, "decimals");
        require(token.totalSupply() == 100, "supply");
        require(token.balanceOf(address(this)) == 100, "balance");
    }

    function testTransferAndInsufficientBalance() public {
        OpenZeppelinERC20HarnessToken token =
            new OpenZeppelinERC20HarnessToken("Harness Token", "HARN", address(this), 100);

        require(token.transfer(address(0xbeef), 25), "transfer");
        require(token.balanceOf(address(this)) == 75, "sender balance");
        require(token.balanceOf(address(0xbeef)) == 25, "recipient balance");

        try token.transfer(address(0xcafe), 200) returns (bool) {
            revert("expected revert");
        } catch (bytes memory reason) {
            _expectCustom(
                reason,
                abi.encodeWithSelector(
                    OpenZeppelinIERC20Errors.ERC20InsufficientBalance.selector,
                    address(this),
                    75,
                    200
                )
            );
        }
    }

    function testApproveTransferFromAndMaxAllowance() public {
        OpenZeppelinERC20HarnessToken token =
            new OpenZeppelinERC20HarnessToken("Harness Token", "HARN", address(this), 100);
        OpenZeppelinERC20Forwarder spender = new OpenZeppelinERC20Forwarder();

        require(token.approve(address(spender), 40), "approve");
        require(token.allowance(address(this), address(spender)) == 40, "allowance");
        require(
            spender.transferFromToken(token, address(this), address(0xbeef), 15),
            "transferFrom"
        );
        require(token.allowance(address(this), address(spender)) == 25, "spent");
        require(token.balanceOf(address(this)) == 85, "from balance");
        require(token.balanceOf(address(0xbeef)) == 15, "to balance");

        require(token.approve(address(spender), type(uint256).max), "approve max");
        require(
            spender.transferFromToken(token, address(this), address(0xcafe), 10),
            "transferFrom max"
        );
        require(
            token.allowance(address(this), address(spender)) == type(uint256).max,
            "max unchanged"
        );
    }

    function testZeroAddressAndAllowanceErrors() public {
        OpenZeppelinERC20HarnessToken token =
            new OpenZeppelinERC20HarnessToken("Harness Token", "HARN", address(this), 100);
        OpenZeppelinERC20Forwarder spender = new OpenZeppelinERC20Forwarder();

        try token.transfer(address(0), 1) returns (bool) {
            revert("expected receiver revert");
        } catch (bytes memory reason) {
            _expectCustom(
                reason,
                abi.encodeWithSelector(
                    OpenZeppelinIERC20Errors.ERC20InvalidReceiver.selector,
                    address(0)
                )
            );
        }

        try spender.transferFromToken(token, address(this), address(0xbeef), 1)
            returns (bool)
        {
            revert("expected allowance revert");
        } catch (bytes memory reason) {
            _expectCustom(
                reason,
                abi.encodeWithSelector(
                    OpenZeppelinIERC20Errors.ERC20InsufficientAllowance.selector,
                    address(spender),
                    0,
                    1
                )
            );
        }
    }
}
