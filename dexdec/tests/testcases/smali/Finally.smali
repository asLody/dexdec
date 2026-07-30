.class public LFinally;
.super Ljava/lang/Object;
.source "Finally.java"


# static fields
.field private static counter:I


# direct methods
.method static constructor <clinit>()V
    .registers 1

    .line 3
    const/4 v0, 0x0

    sput v0, LFinally;->counter:I

    return-void
.end method

.method public constructor <init>()V
    .registers 1

    .line 2
    invoke-direct {p0}, Ljava/lang/Object;-><init>()V

    return-void
.end method

.method public static test(I)I
    .registers 2

    .line 7
    if-eqz p0, :cond_c

    .line 10
    const/16 v0, 0x64

    :try_start_4
    div-int/2addr v0, p0
    :try_end_5
    .catch Ljava/lang/RuntimeException; {:try_start_4 .. :try_end_5} :catch_1c
    .catchall {:try_start_4 .. :try_end_5} :catchall_14

    .line 14
    sget p0, LFinally;->counter:I

    add-int/lit8 p0, p0, 0x1

    sput p0, LFinally;->counter:I

    .line 10
    return v0

    .line 8
    :cond_c
    :try_start_c
    new-instance p0, Ljava/lang/RuntimeException;

    const-string v0, "zero"

    invoke-direct {p0, v0}, Ljava/lang/RuntimeException;-><init>(Ljava/lang/String;)V

    throw p0
    :try_end_14
    .catch Ljava/lang/RuntimeException; {:try_start_c .. :try_end_14} :catch_1c
    .catchall {:try_start_c .. :try_end_14} :catchall_14

    .line 14
    :catchall_14
    move-exception p0

    sget v0, LFinally;->counter:I

    add-int/lit8 v0, v0, 0x1

    sput v0, LFinally;->counter:I

    .line 15
    throw p0

    .line 11
    :catch_1c
    move-exception p0

    .line 12
    nop

    .line 14
    sget p0, LFinally;->counter:I

    add-int/lit8 p0, p0, 0x1

    sput p0, LFinally;->counter:I

    .line 12
    const/4 p0, -0x1

    return p0
.end method
