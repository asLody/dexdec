.class public LSimpleLoop;
.super Ljava/lang/Object;
.source "SimpleLoop.java"


# direct methods
.method public constructor <init>()V
    .registers 1

    .line 2
    invoke-direct {p0}, Ljava/lang/Object;-><init>()V

    return-void
.end method

.method public static sum(I)I
    .registers 3

    .line 4
    nop

    .line 5
    const/4 v0, 0x0

    const/4 v1, 0x0

    .line 6
    :goto_3
    if-ge v0, p0, :cond_9

    .line 7
    add-int/2addr v1, v0

    .line 8
    add-int/lit8 v0, v0, 0x1

    goto :goto_3

    .line 10
    :cond_9
    return v1
.end method
