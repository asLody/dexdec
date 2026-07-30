.class public LForLoop;
.super Ljava/lang/Object;
.source "ForLoop.java"


# direct methods
.method public constructor <init>()V
    .registers 1

    .line 2
    invoke-direct {p0}, Ljava/lang/Object;-><init>()V

    return-void
.end method

.method public static factorial(I)I
    .registers 3

    .line 4
    nop

    .line 5
    const/4 v0, 0x1

    const/4 v1, 0x1

    :goto_3
    if-gt v0, p0, :cond_a

    .line 6
    mul-int v1, v1, v0

    .line 5
    add-int/lit8 v0, v0, 0x1

    goto :goto_3

    .line 8
    :cond_a
    return v1
.end method
