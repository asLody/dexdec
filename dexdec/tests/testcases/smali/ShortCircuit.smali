.class public LShortCircuit;
.super Ljava/lang/Object;
.source "ShortCircuit.java"


# direct methods
.method public constructor <init>()V
    .registers 1

    .line 2
    invoke-direct {p0}, Ljava/lang/Object;-><init>()V

    return-void
.end method

.method public static checkAnd(II)Z
    .registers 2

    .line 5
    if-lez p0, :cond_6

    if-lez p1, :cond_6

    .line 6
    const/4 p0, 0x1

    return p0

    .line 8
    :cond_6
    const/4 p0, 0x0

    return p0
.end method

.method public static checkComplex(IIII)Z
    .registers 4

    .line 21
    if-lez p0, :cond_4

    if-gtz p1, :cond_8

    :cond_4
    if-lez p2, :cond_a

    if-lez p3, :cond_a

    .line 22
    :cond_8
    const/4 p0, 0x1

    return p0

    .line 24
    :cond_a
    const/4 p0, 0x0

    return p0
.end method

.method public static checkNegated(II)Z
    .registers 2

    .line 29
    if-lez p0, :cond_7

    if-gtz p1, :cond_5

    goto :goto_7

    .line 32
    :cond_5
    const/4 p0, 0x0

    return p0

    .line 30
    :cond_7
    :goto_7
    const/4 p0, 0x1

    return p0
.end method

.method public static checkOr(II)Z
    .registers 2

    .line 13
    if-gtz p0, :cond_7

    if-lez p1, :cond_5

    goto :goto_7

    .line 16
    :cond_5
    const/4 p0, 0x0

    return p0

    .line 14
    :cond_7
    :goto_7
    const/4 p0, 0x1

    return p0
.end method
