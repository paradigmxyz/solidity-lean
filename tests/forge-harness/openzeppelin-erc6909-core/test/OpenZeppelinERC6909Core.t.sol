// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {
    OpenZeppelinERC6909Core,
    OpenZeppelinERC6909CoreHarness,
    OpenZeppelinERC6909CoreSpender,
    OpenZeppelinIERC6909
} from "../src/OpenZeppelinERC6909Core.sol";

contract OpenZeppelinERC6909CoreForgeTest {
    function _expectCustom(bytes memory actual, bytes memory expected)
        private
        pure
    {
        require(keccak256(actual) == keccak256(expected), "custom error");
    }

    function testInterfaceIdMintTransferAndBurn() public {
        OpenZeppelinERC6909CoreHarness token =
            new OpenZeppelinERC6909CoreHarness();

        require(token.supportsInterface(type(OpenZeppelinIERC6909).interfaceId), "erc6909 id");
        require(token.supportsInterface(0x01ffc9a7), "erc165 id");
        require(!token.supportsInterface(0xffffffff), "unknown id");

        token.mint(address(this), 7, 11);
        require(token.balanceOf(address(this), 7) == 11, "mint balance");
        require(token.transfer(address(0xbeef), 7, 4), "transfer");
        require(token.balanceOf(address(this), 7) == 7, "sender balance");
        require(token.balanceOf(address(0xbeef), 7) == 4, "receiver balance");
        token.burn(address(this), 7, 2);
        require(token.balanceOf(address(this), 7) == 5, "burn balance");
    }

    function testAllowanceTransferAndInfiniteAllowance() public {
        OpenZeppelinERC6909CoreHarness token =
            new OpenZeppelinERC6909CoreHarness();
        OpenZeppelinERC6909CoreSpender spender =
            new OpenZeppelinERC6909CoreSpender();

        token.mint(address(this), 1, 20);
        require(token.approve(address(spender), 1, 9), "approve");
        require(token.allowance(address(this), address(spender), 1) == 9, "allowance");
        require(
            spender.transferFromToken(token, address(this), address(0xbeef), 1, 4),
            "transferFrom"
        );
        require(token.allowance(address(this), address(spender), 1) == 5, "allowance spent");
        require(token.balanceOf(address(this), 1) == 16, "owner balance");
        require(token.balanceOf(address(0xbeef), 1) == 4, "recipient balance");

        require(token.approve(address(spender), 2, type(uint256).max), "infinite approve");
        token.mint(address(this), 2, 3);
        require(
            spender.transferFromToken(token, address(this), address(0xcafe), 2, 2),
            "infinite transferFrom"
        );
        require(
            token.allowance(address(this), address(spender), 2) == type(uint256).max,
            "infinite allowance kept"
        );
    }

    function testOperatorTransferAndUnset() public {
        OpenZeppelinERC6909CoreHarness token =
            new OpenZeppelinERC6909CoreHarness();
        OpenZeppelinERC6909CoreSpender spender =
            new OpenZeppelinERC6909CoreSpender();

        token.mint(address(this), 9, 6);
        require(token.setOperator(address(spender), true), "set operator");
        require(token.isOperator(address(this), address(spender)), "operator");
        require(
            spender.transferFromToken(token, address(this), address(0xcafe), 9, 5),
            "operator transfer"
        );
        require(token.balanceOf(address(0xcafe), 9) == 5, "operator receiver");
        require(token.allowance(address(this), address(spender), 9) == 0, "no allowance spend");
        require(token.setOperator(address(spender), false), "unset operator");
        require(!token.isOperator(address(this), address(spender)), "operator unset");
    }

    function testErrorsAndRollback() public {
        OpenZeppelinERC6909CoreHarness token =
            new OpenZeppelinERC6909CoreHarness();
        OpenZeppelinERC6909CoreSpender spender =
            new OpenZeppelinERC6909CoreSpender();

        try token.mint(address(0), 1, 1) {
            revert("expected invalid receiver");
        } catch (bytes memory reason) {
            _expectCustom(
                reason,
                abi.encodeWithSelector(
                    OpenZeppelinERC6909Core
                        .ERC6909InvalidReceiver
                        .selector,
                    address(0)
                )
            );
        }

        token.mint(address(this), 3, 5);
        try token.transfer(address(0), 3, 1) returns (bool) {
            revert("expected invalid receiver");
        } catch (bytes memory reason) {
            _expectCustom(
                reason,
                abi.encodeWithSelector(
                    OpenZeppelinERC6909Core
                        .ERC6909InvalidReceiver
                        .selector,
                    address(0)
                )
            );
        }
        require(token.balanceOf(address(this), 3) == 5, "receiver rollback");

        try token.transfer(address(0xbeef), 3, 9) returns (bool) {
            revert("expected insufficient balance");
        } catch (bytes memory reason) {
            _expectCustom(
                reason,
                abi.encodeWithSelector(
                    OpenZeppelinERC6909Core
                        .ERC6909InsufficientBalance
                        .selector,
                    address(this),
                    5,
                    9,
                    3
                )
            );
        }
        require(token.balanceOf(address(this), 3) == 5, "balance rollback");

        try spender.transferFromToken(token, address(this), address(0xbeef), 3, 1)
            returns (bool)
        {
            revert("expected insufficient allowance");
        } catch (bytes memory reason) {
            _expectCustom(
                reason,
                abi.encodeWithSelector(
                    OpenZeppelinERC6909Core
                        .ERC6909InsufficientAllowance
                        .selector,
                    address(spender),
                    0,
                    1,
                    3
                )
            );
        }
        require(token.balanceOf(address(this), 3) == 5, "allowance rollback");

        try token.approve(address(0), 3, 1) returns (bool) {
            revert("expected invalid spender");
        } catch (bytes memory reason) {
            _expectCustom(
                reason,
                abi.encodeWithSelector(
                    OpenZeppelinERC6909Core
                        .ERC6909InvalidSpender
                        .selector,
                    address(0)
                )
            );
        }
    }
}
