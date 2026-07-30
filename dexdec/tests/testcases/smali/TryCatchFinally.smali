.class public LTryCatchFinally;
.super Ljava/lang/Object;
.source "TryCatchFinally.java"


# direct methods
.method public constructor <init>()V
    .registers 1

    .line 2
    invoke-direct {p0}, Ljava/lang/Object;-><init>()V

    return-void
.end method

.method public static simpleTryCatch(I)I
    .registers 1

    .line 5
    if-eqz p0, :cond_4

    .line 8
    const/4 p0, 0x1

    return p0

    .line 6
    :cond_4
    :try_start_4
    new-instance p0, Ljava/lang/RuntimeException;

    invoke-direct {p0}, Ljava/lang/RuntimeException;-><init>()V

    throw p0
    :try_end_a
    .catch Ljava/lang/RuntimeException; {:try_start_4 .. :try_end_a} :catch_a

    .line 9
    :catch_a
    move-exception p0

    .line 10
    const/4 p0, -0x1

    return p0
.end method
