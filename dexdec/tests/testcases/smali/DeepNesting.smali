.class public LDeepNesting;
.super Ljava/lang/Object;
.source "DeepNesting.java"


# direct methods
.method public constructor <init>()V
    .registers 1

    .line 2
    invoke-direct {p0}, Ljava/lang/Object;-><init>()V

    return-void
.end method

.method public static classify(III)I
    .registers 3

    .line 5
    nop

    .line 6
    if-lez p0, :cond_11

    .line 7
    if-lez p1, :cond_b

    .line 8
    if-lez p2, :cond_9

    .line 9
    const/4 p0, 0x1

    goto :goto_16

    .line 11
    :cond_9
    const/4 p0, 0x2

    goto :goto_16

    .line 14
    :cond_b
    if-lez p2, :cond_f

    .line 15
    const/4 p0, 0x3

    goto :goto_16

    .line 17
    :cond_f
    const/4 p0, 0x4

    goto :goto_16

    .line 21
    :cond_11
    if-lez p1, :cond_15

    .line 22
    const/4 p0, 0x5

    goto :goto_16

    .line 24
    :cond_15
    const/4 p0, 0x6

    .line 27
    :goto_16
    return p0
.end method

.method public static conditionalSum(I)I
    .registers 4

    .line 47
    nop

    .line 48
    const/4 v0, 0x0

    const/4 v1, 0x0

    .line 49
    :goto_3
    if-ge v0, p0, :cond_f

    .line 50
    rem-int/lit8 v2, v0, 0x2

    if-nez v2, :cond_b

    .line 51
    add-int/2addr v1, v0

    goto :goto_c

    .line 53
    :cond_b
    sub-int/2addr v1, v0

    .line 55
    :goto_c
    add-int/lit8 v0, v0, 0x1

    goto :goto_3

    .line 57
    :cond_f
    return v1
.end method

.method public static matrixSum(II)I
    .registers 7

    .line 32
    nop

    .line 33
    const/4 v0, 0x0

    const/4 v1, 0x0

    const/4 v2, 0x0

    .line 34
    :goto_4
    if-ge v1, p0, :cond_13

    .line 35
    const/4 v3, 0x0

    .line 36
    :goto_7
    if-ge v3, p1, :cond_10

    .line 37
    mul-int v4, v1, p1

    add-int/2addr v2, v4

    add-int/2addr v2, v3

    .line 38
    add-int/lit8 v3, v3, 0x1

    goto :goto_7

    .line 40
    :cond_10
    add-int/lit8 v1, v1, 0x1

    .line 41
    goto :goto_4

    .line 42
    :cond_13
    return v2
.end method
