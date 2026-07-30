.class public LComplexControlFlow;
.super Ljava/lang/Object;
.source "ComplexControlFlow.java"


# direct methods
.method public constructor <init>()V
    .registers 1

    .line 2
    invoke-direct {p0}, Ljava/lang/Object;-><init>()V

    return-void
.end method

.method public static doWhileClamp(I)I
    .registers 2

    .line 68
    nop

    .line 70
    :cond_1
    if-gez p0, :cond_4

    .line 71
    neg-int p0, p0

    .line 73
    :cond_4
    const/16 v0, 0xa

    if-le p0, v0, :cond_a

    .line 74
    nop

    .line 75
    goto :goto_10

    .line 77
    :cond_a
    add-int/lit8 p0, p0, 0x1

    .line 78
    const/4 v0, 0x5

    if-lt p0, v0, :cond_1

    move v0, p0

    .line 79
    :goto_10
    return v0
.end method

.method public static findInMatrix([[II)I
    .registers 8

    .line 21
    const/4 v0, 0x0

    const/4 v1, 0x0

    :goto_2
    array-length v2, p0

    const/4 v3, -0x1

    if-ge v1, v2, :cond_1f

    .line 22
    aget-object v2, p0, v1

    .line 23
    const/4 v4, 0x0

    :goto_9
    array-length v5, v2

    if-ge v4, v5, :cond_1c

    .line 24
    aget v5, v2, v4

    if-ne v5, p1, :cond_14

    .line 25
    mul-int/lit16 v1, v1, 0x3e8

    add-int/2addr v1, v4

    return v1

    .line 27
    :cond_14
    aget v5, v2, v4

    if-ne v5, v3, :cond_19

    .line 28
    goto :goto_1c

    .line 23
    :cond_19
    add-int/lit8 v4, v4, 0x1

    goto :goto_9

    .line 21
    :cond_1c
    :goto_1c
    add-int/lit8 v1, v1, 0x1

    goto :goto_2

    .line 32
    :cond_1f
    return v3
.end method

.method public static sumUntil([II)I
    .registers 5

    .line 5
    nop

    .line 6
    const/4 v0, 0x0

    const/4 v1, 0x0

    :goto_3
    array-length v2, p0

    if-ge v0, v2, :cond_12

    .line 7
    aget v2, p0, v0

    .line 8
    if-gez v2, :cond_b

    .line 9
    goto :goto_f

    .line 11
    :cond_b
    add-int/2addr v1, v2

    .line 12
    if-le v1, p1, :cond_f

    .line 13
    goto :goto_12

    .line 6
    :cond_f
    :goto_f
    add-int/lit8 v0, v0, 0x1

    goto :goto_3

    .line 16
    :cond_12
    :goto_12
    return v1
.end method

.method public static whileSwitch(I)I
    .registers 4

    .line 37
    nop

    .line 38
    const/4 v0, 0x0

    const/4 v1, 0x0

    .line 39
    :goto_3
    const/4 v2, 0x5

    if-ge v0, v2, :cond_25

    .line 40
    add-int v2, p0, v0

    packed-switch v2, :pswitch_data_26

    .line 51
    add-int/lit8 v1, v1, 0x4

    goto :goto_17

    .line 48
    :pswitch_e
    add-int/lit8 v1, v1, 0x3

    .line 49
    goto :goto_17

    .line 45
    :pswitch_11
    add-int/lit8 v1, v1, 0x2

    .line 46
    goto :goto_17

    .line 42
    :pswitch_14
    add-int/lit8 v1, v1, 0x1

    .line 43
    nop

    .line 54
    :goto_17
    const/4 v2, 0x6

    if-le v1, v2, :cond_1d

    .line 55
    add-int/lit8 v0, v0, 0x1

    .line 56
    goto :goto_3

    .line 58
    :cond_1d
    const/16 v2, 0xa

    if-le v1, v2, :cond_22

    .line 59
    goto :goto_25

    .line 61
    :cond_22
    add-int/lit8 v0, v0, 0x1

    goto :goto_3

    .line 63
    :cond_25
    :goto_25
    return v1

    :pswitch_data_26
    .packed-switch 0x0
        :pswitch_14
        :pswitch_11
        :pswitch_e
    .end packed-switch
.end method
