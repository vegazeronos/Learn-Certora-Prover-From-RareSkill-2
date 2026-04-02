methods{
    function balanceOf(address owner) external returns (uint256) envfree;
    function ownerOf(uint256 tokenId) external returns (address) envfree;
    
    function mint(address to, uint256 tokenId) external;
    function burn(uint256 tokenId) external;
}

definition nonpayable(env e) returns bool = e.msg.value == 0;
definition balanceLimit(address owner) returns bool = balanceOf(owner) < max_uint256;

//TODO: verify mint success -> balance +, owner == minter,
rule mint_success(env e, address owner, uint256 tokenId){
    //precon
    mathint balanceOwnerBefore = balanceOf(owner);
    require balanceOwnerBefore + 1 <= max_uint256;
    

    //action
    mint(e,owner, tokenId);

    //poststate
    mathint balanceOwnerAfter = balanceOf(owner);
    address ownerToken = ownerOf(tokenId);

    //assert
    assert balanceOwnerBefore + 1 == balanceOwnerAfter;
    assert ownerOf(tokenId) == ownerToken;
}

rule mint_revert(env e, address owner, uint256 tokenId){
    //precon
    mathint balanceOwnerBefore = balanceOf(owner);
    address ownerTokenBefore = ownerOf(tokenId);

    //action
    mint@withrevert(e, owner, tokenId);
    bool reverted = lastReverted;

    //poststate
    //assert
    assert reverted => (
        e.msg.value != 0 ||
        balanceOwnerBefore + 1 > max_uint256 ||
        owner == 0 ||
        ownerTokenBefore != 0
    );
}

rule mint(env e, address owner, uint256 tokenId){
    //precon
    require nonpayable(e);
    require balanceLimit(owner);

    address otherOwner;
    uint256 otherTokenId;

    mathint balanceOwnerBefore = balanceOf(owner);
    address ownerTokenIdBefore = ownerOf(tokenId);
    mathint balanceOtherOwnerBefore = balanceOf(otherOwner);
    address ownerOtherTokenIdBefore = ownerOf(otherTokenId);

    require otherTokenId != tokenId;
    require otherOwner != owner;

    //action
    mint@withrevert(e, owner, tokenId);
    bool reverted = lastReverted;

    //poststate
    mathint balanceOwnerAfter = balanceOf(owner);
    address ownerTokenIdAfter = ownerOf(tokenId);
    mathint balanceOtherOwnerAfter = balanceOf(otherOwner);
    address ownerOtherTokenIdAfter = ownerOf(otherTokenId);

    //liveness
    assert !reverted <=> (
        ownerTokenIdBefore == 0 &&
        owner != 0
    );

    //side effect
    assert !reverted => (
        balanceOwnerAfter == balanceOwnerBefore + 1 &&
        ownerTokenIdAfter == owner
    );

    //no side effect
    assert balanceOtherOwnerBefore == balanceOtherOwnerAfter && ownerOtherTokenIdBefore == ownerOtherTokenIdAfter;
}


//TODO: verify burn success -> balance -, owner == burner
rule burn(env e, uint256 tokenId){
    //precon
    uint256 otherTokenId;
    address otherOwner;

    require nonpayable(e);
    address ownerTokenIdBefore = ownerOf(tokenId);
    mathint balanceOwnerTokenIdBefore = balanceOf(ownerTokenIdBefore);
    require balanceOwnerTokenIdBefore > 0;
    address ownerOtherTokenIdBefore = ownerOf(otherTokenId);
    mathint balanceOtherOwnerBefore = balanceOf(otherOwner);

    //action
    burn@withrevert(e, tokenId);
    bool reverted = lastReverted;

    //poststate
    address ownerTokenIdAfter = ownerOf(tokenId);
    mathint balanceOwnerTokenIdAfter = balanceOf(ownerTokenIdBefore);
    address ownerOtherTokenIdAfter = ownerOf(otherTokenId);
    mathint balanceOtherOwnerAfter = balanceOf(otherOwner);

    //assert Liveness
    assert !reverted <=> (
        ownerTokenIdAfter == 0 &&
        ownerTokenIdBefore != 0
    );

    //side effect
    assert !reverted => (
        balanceOwnerTokenIdAfter == balanceOwnerTokenIdBefore - 1 &&
        ownerTokenIdAfter == 0
    );

    //no side effect
    assert ownerOtherTokenIdBefore == ownerOtherTokenIdAfter && balanceOtherOwnerBefore == balanceOtherOwnerAfter;
}