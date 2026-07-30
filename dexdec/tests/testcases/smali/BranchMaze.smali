.class public LBranchMaze;
.super Ljava/lang/Object;
.source "BranchMaze.java"


# direct methods
.method public constructor <init>()V
    .registers 1

    .line 1
    invoke-direct {p0}, Ljava/lang/Object;-><init>()V

    return-void
.end method

.method public static classify(III)I
    .registers 5

    .line 4
    const/4 v0, 0x2

    if-lez p0, :cond_9

    if-ltz p1, :cond_7

    if-nez p2, :cond_9

    .line 5
    :cond_7
    const/4 v1, 0x1

    goto :goto_13

    .line 6
    :cond_9
    if-eqz p0, :cond_12

    if-lez p1, :cond_10

    if-lez p2, :cond_10

    goto :goto_12

    .line 9
    :cond_10
    const/4 v1, 0x3

    goto :goto_13

    .line 7
    :cond_12
    :goto_12
    const/4 v1, 0x2

    .line 12
    :goto_13
    if-ne v1, v0, :cond_1b

    if-lt p0, p1, :cond_19

    if-gez p2, :cond_1b

    .line 13
    :cond_19
    add-int/lit8 v1, v1, 0xa

    .line 16
    :cond_1b
    return v1
.end method
