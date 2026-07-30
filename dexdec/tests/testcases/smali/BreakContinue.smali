.class public LBreakContinue;
.super Ljava/lang/Object;
.source "BreakContinue.java"


# direct methods
.method public constructor <init>()V
    .registers 1

    .line 2
    invoke-direct {p0}, Ljava/lang/Object;-><init>()V

    return-void
.end method

.method public static findFirst([II)I
    .registers 4

    .line 5
    nop

    .line 6
    const/4 v0, 0x0

    .line 7
    :goto_2
    array-length v1, p0

    if-ge v0, v1, :cond_e

    .line 8
    aget v1, p0, v0

    if-ne v1, p1, :cond_b

    .line 9
    nop

    .line 10
    goto :goto_f

    .line 12
    :cond_b
    add-int/lit8 v0, v0, 0x1

    goto :goto_2

    .line 7
    :cond_e
    const/4 v0, -0x1

    .line 14
    :goto_f
    return v0
.end method

.method public static findPair([II)Z
    .registers 8

    .line 34
    const/4 v0, 0x0

    const/4 v1, 0x0

    .line 35
    :goto_2
    array-length v2, p0

    if-ge v1, v2, :cond_1a

    .line 36
    add-int/lit8 v2, v1, 0x1

    move v3, v2

    .line 37
    :goto_8
    array-length v4, p0

    if-ge v3, v4, :cond_17

    .line 38
    aget v4, p0, v1

    aget v5, p0, v3

    add-int/2addr v4, v5

    if-ne v4, p1, :cond_14

    .line 39
    const/4 p0, 0x1

    return p0

    .line 41
    :cond_14
    add-int/lit8 v3, v3, 0x1

    goto :goto_8

    .line 43
    :cond_17
    nop

    .line 44
    move v1, v2

    goto :goto_2

    .line 45
    :cond_1a
    return v0
.end method

.method public static sumPositive([I)I
    .registers 4

    .line 19
    nop

    .line 20
    const/4 v0, 0x0

    const/4 v1, 0x0

    .line 21
    :goto_3
    array-length v2, p0

    if-ge v0, v2, :cond_13

    .line 22
    aget v2, p0, v0

    if-gtz v2, :cond_d

    .line 23
    add-int/lit8 v0, v0, 0x1

    .line 24
    goto :goto_3

    .line 26
    :cond_d
    aget v2, p0, v0

    add-int/2addr v1, v2

    .line 27
    add-int/lit8 v0, v0, 0x1

    goto :goto_3

    .line 29
    :cond_13
    return v1
.end method
