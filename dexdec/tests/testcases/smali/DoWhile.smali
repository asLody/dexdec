.class public LDoWhile;
.super Ljava/lang/Object;
.source "DoWhile.java"


# direct methods
.method public constructor <init>()V
    .registers 1

    .line 2
    invoke-direct {p0}, Ljava/lang/Object;-><init>()V

    return-void
.end method

.method public static countDigits(I)I
    .registers 2

    .line 4
    const/4 v0, 0x0

    .line 6
    :cond_1
    add-int/lit8 v0, v0, 0x1

    .line 7
    div-int/lit8 p0, p0, 0xa

    .line 8
    if-gtz p0, :cond_1

    .line 9
    return v0
.end method
