.class public LSynchronizedAdvanced;
.super Ljava/lang/Object;
.source "SynchronizedAdvanced.java"


# static fields
.field private static lock1:Ljava/lang/Object;

.field private static lock2:Ljava/lang/Object;

.field private static value:I


# direct methods
.method static constructor <clinit>()V
    .registers 1

    .line 3
    new-instance v0, Ljava/lang/Object;

    invoke-direct {v0}, Ljava/lang/Object;-><init>()V

    sput-object v0, LSynchronizedAdvanced;->lock1:Ljava/lang/Object;

    .line 4
    new-instance v0, Ljava/lang/Object;

    invoke-direct {v0}, Ljava/lang/Object;-><init>()V

    sput-object v0, LSynchronizedAdvanced;->lock2:Ljava/lang/Object;

    .line 5
    const/4 v0, 0x0

    sput v0, LSynchronizedAdvanced;->value:I

    return-void
.end method

.method public constructor <init>()V
    .registers 1

    .line 2
    invoke-direct {p0}, Ljava/lang/Object;-><init>()V

    return-void
.end method

.method public static deepNesting([I)I
    .registers 6

    .line 76
    nop

    .line 77
    const/4 v0, 0x0

    const/4 v1, 0x0

    :goto_3
    array-length v2, p0

    if-ge v0, v2, :cond_1b

    .line 78
    sget-object v2, LSynchronizedAdvanced;->lock1:Ljava/lang/Object;

    monitor-enter v2

    .line 80
    :try_start_9
    aget v3, p0, v0

    const/16 v4, 0xa

    div-int/2addr v4, v3
    :try_end_e
    .catch Ljava/lang/ArithmeticException; {:try_start_9 .. :try_end_e} :catch_12
    .catchall {:try_start_9 .. :try_end_e} :catchall_10

    add-int/2addr v1, v4

    .line 83
    goto :goto_15

    .line 84
    :catchall_10
    move-exception p0

    goto :goto_19

    .line 81
    :catch_12
    move-exception v3

    .line 82
    add-int/lit8 v1, v1, -0x1

    .line 84
    :goto_15
    :try_start_15
    monitor-exit v2

    .line 77
    add-int/lit8 v0, v0, 0x1

    goto :goto_3

    .line 84
    :goto_19
    monitor-exit v2
    :try_end_1a
    .catchall {:try_start_15 .. :try_end_1a} :catchall_10

    throw p0

    .line 86
    :cond_1b
    return v1
.end method

.method private static helper(I)I
    .registers 1

    .line 118
    mul-int/lit8 p0, p0, 0x2

    return p0
.end method

.method public static sequentialSync(II)I
    .registers 4

    .line 50
    sget-object v0, LSynchronizedAdvanced;->lock1:Ljava/lang/Object;

    monitor-enter v0

    .line 51
    add-int/lit8 p0, p0, 0x1

    .line 52
    :try_start_5
    monitor-exit v0
    :try_end_6
    .catchall {:try_start_5 .. :try_end_6} :catchall_f

    .line 53
    sget-object v1, LSynchronizedAdvanced;->lock2:Ljava/lang/Object;

    monitor-enter v1

    .line 54
    add-int/2addr p0, p1

    .line 55
    :try_start_a
    monitor-exit v1

    .line 56
    return p0

    .line 55
    :catchall_c
    move-exception p0

    monitor-exit v1
    :try_end_e
    .catchall {:try_start_a .. :try_end_e} :catchall_c

    throw p0

    .line 52
    :catchall_f
    move-exception p0

    :try_start_10
    monitor-exit v0
    :try_end_11
    .catchall {:try_start_10 .. :try_end_11} :catchall_f

    throw p0
.end method

.method public static syncMultiCatch(I)I
    .registers 3

    .line 139
    sget-object v0, LSynchronizedAdvanced;->lock1:Ljava/lang/Object;

    monitor-enter v0

    .line 141
    if-ltz p0, :cond_10

    .line 144
    const/16 v1, 0x64

    :try_start_7
    div-int/2addr v1, p0
    :try_end_8
    .catch Ljava/lang/ArithmeticException; {:try_start_7 .. :try_end_8} :catch_e
    .catch Ljava/lang/IllegalArgumentException; {:try_start_7 .. :try_end_8} :catch_c
    .catchall {:try_start_7 .. :try_end_8} :catchall_a

    :try_start_8
    monitor-exit v0
    :try_end_9
    .catchall {:try_start_8 .. :try_end_9} :catchall_a

    return v1

    .line 150
    :catchall_a
    move-exception p0

    goto :goto_1c

    .line 147
    :catch_c
    move-exception p0

    goto :goto_16

    .line 145
    :catch_e
    move-exception p0

    goto :goto_19

    .line 142
    :cond_10
    :try_start_10
    new-instance p0, Ljava/lang/IllegalArgumentException;

    invoke-direct {p0}, Ljava/lang/IllegalArgumentException;-><init>()V

    throw p0
    :try_end_16
    .catch Ljava/lang/ArithmeticException; {:try_start_10 .. :try_end_16} :catch_e
    .catch Ljava/lang/IllegalArgumentException; {:try_start_10 .. :try_end_16} :catch_c
    .catchall {:try_start_10 .. :try_end_16} :catchall_a

    .line 148
    :goto_16
    :try_start_16
    monitor-exit v0

    const/4 p0, -0x2

    return p0

    .line 146
    :goto_19
    monitor-exit v0

    const/4 p0, -0x1

    return p0

    .line 150
    :goto_1c
    monitor-exit v0
    :try_end_1d
    .catchall {:try_start_16 .. :try_end_1d} :catchall_a

    throw p0
.end method

.method public static syncOnClass(I)I
    .registers 2

    .line 131
    const-class v0, LSynchronizedAdvanced;

    monitor-enter v0

    .line 132
    :try_start_3
    sput p0, LSynchronizedAdvanced;->value:I

    .line 133
    monitor-exit v0
    :try_end_6
    .catchall {:try_start_3 .. :try_end_6} :catchall_9

    .line 134
    sget p0, LSynchronizedAdvanced;->value:I

    return p0

    .line 133
    :catchall_9
    move-exception p0

    :try_start_a
    monitor-exit v0
    :try_end_b
    .catchall {:try_start_a .. :try_end_b} :catchall_9

    throw p0
.end method

.method public static syncWhileLoop(I)I
    .registers 3

    .line 37
    nop

    .line 38
    sget-object v0, LSynchronizedAdvanced;->lock1:Ljava/lang/Object;

    monitor-enter v0

    const/4 v1, 0x0

    .line 39
    :goto_5
    if-lez p0, :cond_c

    .line 40
    add-int/lit8 v1, v1, 0x1

    .line 41
    :try_start_9
    div-int/lit8 p0, p0, 0x2

    goto :goto_5

    .line 43
    :cond_c
    monitor-exit v0

    .line 44
    return v1

    .line 43
    :catchall_e
    move-exception p0

    monitor-exit v0
    :try_end_10
    .catchall {:try_start_9 .. :try_end_10} :catchall_e

    goto :goto_12

    :goto_11
    throw p0

    :goto_12
    goto :goto_11
.end method

.method public static syncWithBreak([I)I
    .registers 5

    .line 9
    nop

    .line 10
    sget-object v0, LSynchronizedAdvanced;->lock1:Ljava/lang/Object;

    monitor-enter v0

    .line 11
    const/4 v1, 0x0

    const/4 v2, 0x0

    :goto_6
    :try_start_6
    array-length v3, p0

    if-ge v1, v3, :cond_14

    .line 12
    aget v3, p0, v1

    if-gez v3, :cond_e

    .line 13
    goto :goto_14

    .line 15
    :cond_e
    aget v3, p0, v1

    add-int/2addr v2, v3

    .line 11
    add-int/lit8 v1, v1, 0x1

    goto :goto_6

    .line 17
    :cond_14
    :goto_14
    monitor-exit v0

    .line 18
    return v2

    .line 17
    :catchall_16
    move-exception p0

    monitor-exit v0
    :try_end_18
    .catchall {:try_start_6 .. :try_end_18} :catchall_16

    goto :goto_1a

    :goto_19
    throw p0

    :goto_1a
    goto :goto_19
.end method

.method public static syncWithCall(I)I
    .registers 2

    .line 112
    sget-object v0, LSynchronizedAdvanced;->lock1:Ljava/lang/Object;

    monitor-enter v0

    .line 113
    :try_start_3
    invoke-static {p0}, LSynchronizedAdvanced;->helper(I)I

    move-result p0

    monitor-exit v0

    return p0

    .line 114
    :catchall_9
    move-exception p0

    monitor-exit v0
    :try_end_b
    .catchall {:try_start_3 .. :try_end_b} :catchall_9

    throw p0
.end method

.method public static syncWithContinue([I)I
    .registers 5

    .line 23
    nop

    .line 24
    sget-object v0, LSynchronizedAdvanced;->lock1:Ljava/lang/Object;

    monitor-enter v0

    .line 25
    const/4 v1, 0x0

    const/4 v2, 0x0

    :goto_6
    :try_start_6
    array-length v3, p0

    if-ge v1, v3, :cond_14

    .line 26
    aget v3, p0, v1

    if-nez v3, :cond_e

    .line 27
    goto :goto_11

    .line 29
    :cond_e
    aget v3, p0, v1

    add-int/2addr v2, v3

    .line 25
    :goto_11
    add-int/lit8 v1, v1, 0x1

    goto :goto_6

    .line 31
    :cond_14
    monitor-exit v0

    .line 32
    return v2

    .line 31
    :catchall_16
    move-exception p0

    monitor-exit v0
    :try_end_18
    .catchall {:try_start_6 .. :try_end_18} :catchall_16

    goto :goto_1a

    :goto_19
    throw p0

    :goto_1a
    goto :goto_19
.end method

.method public static syncWithFinally(I)I
    .registers 3

    .line 61
    nop

    .line 62
    sget-object v0, LSynchronizedAdvanced;->lock1:Ljava/lang/Object;

    monitor-enter v0

    .line 64
    const/16 v1, 0x64

    :try_start_6
    div-int/2addr v1, p0
    :try_end_7
    .catch Ljava/lang/ArithmeticException; {:try_start_6 .. :try_end_7} :catch_11
    .catchall {:try_start_6 .. :try_end_7} :catchall_c

    .line 68
    :try_start_7
    sput v1, LSynchronizedAdvanced;->value:I

    .line 69
    :goto_9
    goto :goto_17

    .line 70
    :catchall_a
    move-exception p0

    goto :goto_19

    .line 68
    :catchall_c
    move-exception p0

    const/4 v1, 0x0

    sput v1, LSynchronizedAdvanced;->value:I

    .line 69
    throw p0

    .line 65
    :catch_11
    move-exception p0

    .line 66
    nop

    .line 68
    const/4 v1, -0x1

    sput v1, LSynchronizedAdvanced;->value:I

    goto :goto_9

    .line 70
    :goto_17
    monitor-exit v0

    .line 71
    return v1

    .line 70
    :goto_19
    monitor-exit v0
    :try_end_1a
    .catchall {:try_start_7 .. :try_end_1a} :catchall_a

    goto :goto_1c

    :goto_1b
    throw p0

    :goto_1c
    goto :goto_1b
.end method

.method public static syncWithSwitch(I)I
    .registers 2

    .line 92
    sget-object v0, LSynchronizedAdvanced;->lock1:Ljava/lang/Object;

    monitor-enter v0

    .line 93
    packed-switch p0, :pswitch_data_18

    .line 104
    const/4 p0, 0x0

    goto :goto_13

    .line 101
    :pswitch_8
    nop

    .line 102
    const/16 p0, 0x1e

    goto :goto_13

    .line 98
    :pswitch_c
    nop

    .line 99
    const/16 p0, 0x14

    goto :goto_13

    .line 95
    :pswitch_10
    nop

    .line 96
    const/16 p0, 0xa

    .line 106
    :goto_13
    :try_start_13
    monitor-exit v0

    .line 107
    return p0

    .line 106
    :catchall_15
    move-exception p0

    monitor-exit v0
    :try_end_17
    .catchall {:try_start_13 .. :try_end_17} :catchall_15

    throw p0

    :pswitch_data_18
    .packed-switch 0x1
        :pswitch_10
        :pswitch_c
        :pswitch_8
    .end packed-switch
.end method


# virtual methods
.method public syncOnThis(I)I
    .registers 2

    .line 123
    monitor-enter p0

    .line 124
    :try_start_1
    sput p1, LSynchronizedAdvanced;->value:I

    .line 125
    monitor-exit p0
    :try_end_4
    .catchall {:try_start_1 .. :try_end_4} :catchall_7

    .line 126
    sget p1, LSynchronizedAdvanced;->value:I

    return p1

    .line 125
    :catchall_7
    move-exception p1

    :try_start_8
    monitor-exit p0
    :try_end_9
    .catchall {:try_start_8 .. :try_end_9} :catchall_7

    throw p1
.end method
