# Inode quota increase request — pl0414-02

**To:** support-hpc@man.poznan.pl
**Subject:** Increase inode quota for project pl0414-02 on /mnt/storage_5/scratch

Dear support,

I am running a Lean 4 + Mathlib formalization project on Eagle under
project pl0414-02 (uid nasqret, project ID 10041402). The Lean
toolchain alone contains approximately 12,800 files, and Mathlib's
build cache adds another ~25,000 `.olean` files. Both are required
even for a single `lake env lean` invocation.

I have hit the default project file (inode) quota at 13,540 files
in /mnt/storage_5/scratch even though my block usage is only 526 MB
of the 1 TB project allocation:

```
$ lfs quota -h -p 10041402 /mnt/storage_5/scratch
Disk quotas for prj 10041402 (pid 10041402):
  Filesystem    used   quota   limit   grace   files   quota   limit   grace
/mnt/storage_5/scratch
                526.5M     0k     1T       -   13540       0       0       -
pid 10041402 is using default file quota setting
```

I would like to request an inode quota increase to **at least
500,000 files** (Mathlib + a typical formalisation tree fits
comfortably in this range; more headroom would help).

The block quota of 1 TB is more than sufficient — the issue is purely
the file-count limit, which the default 13k cannot accommodate the
Lean ecosystem.

Thank you,
Bartosz Naskręcki (nasqret)
project pl0414-02
