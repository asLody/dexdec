.class public LHardcoreControlFlow;
.super Ljava/lang/Object;
.source "HardcoreControlFlow.java"


# direct methods
.method public constructor <init>()V
    .registers 1

    .line 1
    invoke-direct {p0}, Ljava/lang/Object;-><init>()V

    return-void
.end method

.method private check(I)Z
    .registers 2

    .line 112
    if-lez p1, :cond_4

    const/4 p1, 0x1

    goto :goto_5

    :cond_4
    const/4 p1, 0x0

    :goto_5
    return p1
.end method

.method private modify(I)Z
    .registers 2

    .line 113
    rem-int/lit8 p1, p1, 0x2

    if-nez p1, :cond_6

    const/4 p1, 0x1

    goto :goto_7

    :cond_6
    const/4 p1, 0x0

    :goto_7
    return p1
.end method


# virtual methods
.method public complexLogic(II)Z
    .registers 4

    .line 106
    invoke-direct {p0, p1}, LHardcoreControlFlow;->check(I)Z

    move-result v0

    if-nez v0, :cond_1b

    invoke-direct {p0, p1}, LHardcoreControlFlow;->modify(I)Z

    move-result p1

    if-eqz p1, :cond_12

    invoke-direct {p0, p2}, LHardcoreControlFlow;->check(I)Z

    move-result p1

    if-nez p1, :cond_1b

    :cond_12
    invoke-direct {p0, p2}, LHardcoreControlFlow;->modify(I)Z

    move-result p1

    if-eqz p1, :cond_19

    goto :goto_1b

    .line 109
    :cond_19
    const/4 p1, 0x0

    return p1

    .line 107
    :cond_1b
    :goto_1b
    const/4 p1, 0x1

    return p1
.end method

.method public exceptionSpaghetti(II)I
    .registers 4

    .line 77
    nop

    .line 79
    const/4 v0, 0x0

    if-lez p1, :cond_23

    .line 81
    :try_start_4
    div-int/2addr p1, p2
    :try_end_5
    .catch Ljava/lang/ArithmeticException; {:try_start_4 .. :try_end_5} :catch_1b
    .catchall {:try_start_4 .. :try_end_5} :catchall_19

    .line 82
    const/16 p2, 0xa

    if-le p1, p2, :cond_11

    .line 87
    add-int/lit8 p2, p1, 0x64

    .line 97
    if-lez p2, :cond_10

    .line 98
    mul-int/lit8 p2, p2, 0x2

    return p2

    .line 82
    :cond_10
    return p1

    .line 87
    :cond_11
    add-int/lit8 p1, p1, 0x64

    .line 88
    nop

    .line 97
    if-lez p1, :cond_3a

    .line 98
    :goto_16
    mul-int/lit8 p1, p1, 0x2

    return p1

    .line 87
    :catchall_19
    move-exception p1

    goto :goto_20

    .line 83
    :catch_1b
    move-exception p1

    .line 84
    nop

    .line 85
    :try_start_1d
    throw p1
    :try_end_1e
    .catchall {:try_start_1d .. :try_end_1e} :catchall_1e

    .line 87
    :catchall_1e
    move-exception p1

    const/4 v0, -0x1

    :goto_20
    add-int/lit8 v0, v0, 0x64

    .line 88
    :try_start_22
    throw p1

    .line 90
    :cond_23
    new-instance p1, Ljava/lang/IllegalArgumentException;

    invoke-direct {p1}, Ljava/lang/IllegalArgumentException;-><init>()V

    throw p1
    :try_end_29
    .catch Ljava/lang/IllegalArgumentException; {:try_start_22 .. :try_end_29} :catch_34
    .catch Ljava/lang/ArithmeticException; {:try_start_22 .. :try_end_29} :catch_30
    .catchall {:try_start_22 .. :try_end_29} :catchall_29

    .line 97
    :catchall_29
    move-exception p1

    if-lez v0, :cond_2f

    .line 98
    mul-int/lit8 v0, v0, 0x2

    return v0

    .line 100
    :cond_2f
    throw p1

    .line 94
    :catch_30
    move-exception p1

    .line 95
    nop

    .line 97
    const/4 p1, -0x2

    goto :goto_3a

    .line 92
    :catch_34
    move-exception p1

    .line 93
    add-int/lit8 p1, v0, -0x64

    .line 97
    if-lez p1, :cond_3a

    .line 98
    goto :goto_16

    .line 101
    :cond_3a
    :goto_3a
    return p1
.end method

.method public labeledBreaks([[I)I
    .registers 10

    .line 43
    nop

    .line 44
    const/4 v0, 0x0

    const/4 v1, 0x0

    const/4 v2, 0x0

    :goto_4
    array-length v3, p1

    if-ge v1, v3, :cond_3b

    .line 45
    aget-object v3, p1, v1

    if-nez v3, :cond_c

    goto :goto_38

    .line 47
    :cond_c
    const/4 v3, 0x0

    :goto_d
    aget-object v4, p1, v1

    array-length v4, v4

    if-ge v3, v4, :cond_38

    .line 48
    aget-object v4, p1, v1

    aget v4, v4, v3

    .line 50
    const/4 v5, -0x1

    if-ne v4, v5, :cond_1a

    .line 51
    goto :goto_3b

    .line 53
    :cond_1a
    const/4 v5, -0x2

    if-ne v4, v5, :cond_1e

    .line 54
    goto :goto_38

    .line 56
    :cond_1e
    const/4 v5, -0x3

    if-ne v4, v5, :cond_22

    .line 57
    goto :goto_38

    .line 60
    :cond_22
    const/16 v5, 0x64

    if-le v4, v5, :cond_34

    .line 61
    const/4 v5, 0x0

    :goto_27
    if-ge v5, v4, :cond_34

    .line 62
    mul-int v6, v5, v3

    const/16 v7, 0x3e8

    if-le v6, v7, :cond_31

    .line 63
    add-int/2addr v2, v5

    .line 64
    goto :goto_38

    .line 61
    :cond_31
    add-int/lit8 v5, v5, 0x1

    goto :goto_27

    .line 69
    :cond_34
    add-int/2addr v2, v4

    .line 47
    add-int/lit8 v3, v3, 0x1

    goto :goto_d

    .line 44
    :cond_38
    :goto_38
    add-int/lit8 v1, v1, 0x1

    goto :goto_4

    .line 72
    :cond_3b
    :goto_3b
    return v2
.end method

.method public stateMachine([I)I
    .registers 8

    .line 4
    nop

    .line 5
    nop

    .line 6
    const/4 v0, 0x0

    const/4 v1, 0x0

    const/4 v2, 0x0

    const/4 v3, 0x0

    .line 8
    :goto_6
    array-length v4, p1

    if-ge v1, v4, :cond_2a

    .line 9
    aget v4, p1, v1

    .line 10
    const/4 v5, 0x1

    packed-switch v3, :pswitch_data_2c

    .line 34
    const/4 p1, -0x1

    return p1

    .line 30
    :pswitch_11
    sub-int/2addr v2, v4

    .line 31
    nop

    .line 32
    const/4 v3, 0x0

    goto :goto_27

    .line 22
    :pswitch_15
    if-nez v4, :cond_19

    .line 23
    const/4 v3, 0x0

    goto :goto_27

    .line 25
    :cond_19
    mul-int/lit8 v2, v2, 0x2

    .line 26
    add-int/lit8 v1, v1, 0x1

    .line 28
    goto :goto_27

    .line 12
    :pswitch_1e
    if-lez v4, :cond_24

    .line 13
    nop

    .line 14
    add-int/2addr v2, v4

    const/4 v3, 0x1

    goto :goto_27

    .line 15
    :cond_24
    if-gez v4, :cond_29

    .line 16
    const/4 v3, 0x2

    .line 36
    :goto_27
    add-int/2addr v1, v5

    .line 37
    goto :goto_6

    .line 18
    :cond_29
    return v2

    .line 38
    :cond_2a
    return v2

    nop

    :pswitch_data_2c
    .packed-switch 0x0
        :pswitch_1e
        :pswitch_15
        :pswitch_11
    .end packed-switch
.end method
