.class public LNestedLoopBranches;
.super Ljava/lang/Object;
.source "NestedLoopBranches.java"


# direct methods
.method public constructor <init>()V
    .registers 1

    .line 1
    invoke-direct {p0}, Ljava/lang/Object;-><init>()V

    return-void
.end method

.method public static compute([I[[II)I
    .registers 11

    .line 3
    nop

    .line 4
    const/4 v0, 0x0

    const/4 v1, 0x0

    const/4 v2, 0x0

    :goto_4
    array-length v3, p0

    if-ge v1, v3, :cond_2c

    .line 5
    aget v3, p0, v1

    if-gez v3, :cond_c

    .line 6
    goto :goto_29

    .line 8
    :cond_c
    aget-object v3, p1, v1

    .line 9
    const/4 v4, 0x0

    :goto_f
    array-length v5, v3

    const/16 v6, 0x3e8

    if-ge v4, v5, :cond_26

    .line 10
    aget v5, v3, v4

    .line 11
    if-ne v5, p2, :cond_1a

    .line 12
    add-int/2addr v2, v5

    return v2

    .line 14
    :cond_1a
    rem-int/lit8 v7, v5, 0x2

    if-nez v7, :cond_1f

    .line 15
    goto :goto_23

    .line 17
    :cond_1f
    add-int/2addr v2, v5

    .line 18
    if-le v2, v6, :cond_23

    .line 19
    goto :goto_26

    .line 9
    :cond_23
    :goto_23
    add-int/lit8 v4, v4, 0x1

    goto :goto_f

    .line 22
    :cond_26
    :goto_26
    if-le v2, v6, :cond_29

    .line 23
    goto :goto_2c

    .line 4
    :cond_29
    :goto_29
    add-int/lit8 v1, v1, 0x1

    goto :goto_4

    .line 26
    :cond_2c
    :goto_2c
    return v2
.end method
