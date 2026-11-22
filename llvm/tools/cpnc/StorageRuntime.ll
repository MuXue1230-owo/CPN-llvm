; Sparse lifetime registrations for Core's native x86-64 target.
; Fields: list link, root, parent, address, original type, current type,
; initial generation, current generation, destructor, capacity, alignment,
; parent's generation at birth and a destruction-in-progress flag.
%cpn.slot = type { ptr, ptr, ptr, ptr, ptr, ptr, i64, i64, ptr, i64, i64, i64, i1 }
@cpn.slots = internal thread_local global ptr null
@cpn.epoch = internal thread_local global i64 1
declare ptr @malloc(i64)
declare void @free(ptr)
declare void @llvm.trap()

define internal i64 @cpn.new.generation() {
  %gen = load i64, ptr @cpn.epoch
  %next = add i64 %gen, 2
  %overflow = icmp ult i64 %next, %gen
  br i1 %overflow, label %exhausted, label %done
exhausted:
  call void @llvm.trap()
  unreachable
done:
  store i64 %next, ptr @cpn.epoch
  ret i64 %gen
}

define internal i64 @cpn.generation(ptr %slot, i1 %original) {
  %absent = icmp eq ptr %slot, null
  br i1 %absent, label %none, label %present
none:
  ret i64 0
present:
  %birth = getelementptr %cpn.slot, ptr %slot, i32 0, i32 6
  %stamp = getelementptr %cpn.slot, ptr %slot, i32 0, i32 7
  %field = select i1 %original, ptr %birth, ptr %stamp
  %value = load i64, ptr %field
  ret i64 %value
}

define internal void @cpn.slot.begin(ptr %s, ptr %addr, ptr %ty, ptr %drop, i64 %size, i64 %align, ptr %parent, i64 %parentgen) {
  %hasparent = icmp ne ptr %parent, null
  br i1 %hasparent, label %child, label %init
child:
  %ownerp = getelementptr %cpn.slot, ptr %parent, i32 0, i32 1
  %owner = load ptr, ptr %ownerp
  br label %init
init:
  %root = phi ptr [ %s, %0 ], [ %owner, %child ]
  %gen = call i64 @cpn.new.generation()
  %root.slot = getelementptr %cpn.slot, ptr %s, i32 0, i32 1
  store ptr %root, ptr %root.slot
  %parent.slot = getelementptr %cpn.slot, ptr %s, i32 0, i32 2
  store ptr %parent, ptr %parent.slot
  %address.slot = getelementptr %cpn.slot, ptr %s, i32 0, i32 3
  store ptr %addr, ptr %address.slot
  %original.type.slot = getelementptr %cpn.slot, ptr %s, i32 0, i32 4
  store ptr %ty, ptr %original.type.slot
  %current.type.slot = getelementptr %cpn.slot, ptr %s, i32 0, i32 5
  store ptr %ty, ptr %current.type.slot
  %birth.slot = getelementptr %cpn.slot, ptr %s, i32 0, i32 6
  store i64 %gen, ptr %birth.slot
  %generation.slot = getelementptr %cpn.slot, ptr %s, i32 0, i32 7
  store i64 %gen, ptr %generation.slot
  %destructor.slot = getelementptr %cpn.slot, ptr %s, i32 0, i32 8
  store ptr %drop, ptr %destructor.slot
  %capacity.slot = getelementptr %cpn.slot, ptr %s, i32 0, i32 9
  store i64 %size, ptr %capacity.slot
  %alignment.slot = getelementptr %cpn.slot, ptr %s, i32 0, i32 10
  store i64 %align, ptr %alignment.slot
  %parent.generation.slot = getelementptr %cpn.slot, ptr %s, i32 0, i32 11
  store i64 %parentgen, ptr %parent.generation.slot
  %busy = getelementptr %cpn.slot, ptr %s, i32 0, i32 12
  store i1 false, ptr %busy
  ret void
}

define internal void @cpn.slot.link(ptr %s) {
  %next = load ptr, ptr @cpn.slots
  store ptr %next, ptr %s
  store ptr %s, ptr @cpn.slots
  ret void
}

define internal ptr @cpn.slot.find(ptr %addr, ptr %ty, ptr %parent, i1 %checkparent) {
  %head = load ptr, ptr @cpn.slots
  br label %scan
scan:
  %s = phi ptr [ %head, %0 ], [ %next, %advance ]
  %empty = icmp eq ptr %s, null
  br i1 %empty, label %done, label %test
test:
  %ap = getelementptr %cpn.slot, ptr %s, i32 0, i32 3
  %a = load ptr, ptr %ap
  %sameaddr = icmp eq ptr %a, %addr
  %tp = getelementptr %cpn.slot, ptr %s, i32 0, i32 4
  %t = load ptr, ptr %tp
  %original = icmp eq ptr %t, %ty
  %cp = getelementptr %cpn.slot, ptr %s, i32 0, i32 5
  %c = load ptr, ptr %cp
  %current = icmp eq ptr %c, %ty
  %either = or i1 %current, %original
  %pp = getelementptr %cpn.slot, ptr %s, i32 0, i32 2
  %p = load ptr, ptr %pp
  %sameparent = icmp eq ptr %p, %parent
  %child = and i1 %original, %sameparent
  %matchtype = select i1 %checkparent, i1 %child, i1 %either
  %match = and i1 %sameaddr, %matchtype
  br i1 %match, label %done, label %advance
advance:
  %next = load ptr, ptr %s
  br label %scan
done:
  ret ptr %s
}

define internal ptr @cpn.slot.child(ptr %parent, ptr %addr, ptr %ty, ptr %drop, i64 %size, i64 %align) {
  %missing = icmp eq ptr %parent, null
  br i1 %missing, label %none, label %lookup
none:
  ret ptr null
lookup:
  %parentgen = call i64 @cpn.generation(ptr %parent, i1 false)
  %found = call ptr @cpn.slot.find(ptr %addr, ptr %ty, ptr %parent, i1 true)
  %fresh = icmp eq ptr %found, null
  br i1 %fresh, label %allocate, label %test
test:
  %gp = getelementptr %cpn.slot, ptr %found, i32 0, i32 11
  %old = load i64, ptr %gp
  %same = icmp eq i64 %old, %parentgen
  br i1 %same, label %keep, label %init
keep:
  ret ptr %found
allocate:
  %mem = call ptr @malloc(i64 ptrtoint (ptr getelementptr (%cpn.slot, ptr null, i32 1) to i64))
  %oom = icmp eq ptr %mem, null
  br i1 %oom, label %failed, label %link
failed:
  call void @llvm.trap()
  unreachable
link:
  call void @cpn.slot.link(ptr %mem)
  br label %init
init:
  %s = phi ptr [ %found, %test ], [ %mem, %link ]
  call void @cpn.slot.begin(ptr %s, ptr %addr, ptr %ty, ptr %drop, i64 %size, i64 %align, ptr %parent, i64 %parentgen)
  ret ptr %s
}

; End all dependent views, including descendants that were abandoned.
define internal void @cpn.slot.invalidate(ptr %s) {
  %stamp = getelementptr %cpn.slot, ptr %s, i32 0, i32 7
  %value = load i64, ptr %stamp
  %ended = and i64 %value, -2
  store i64 %ended, ptr %stamp
  %head = load ptr, ptr @cpn.slots
  br label %scan
scan:
  %n = phi ptr [%head, %0], [%next, %advance]
  %done = icmp eq ptr %n, null
  br i1 %done, label %end, label %test
test:
  %pp = getelementptr %cpn.slot, ptr %n, i32 0, i32 2
  %parent = load ptr, ptr %pp
  %child = icmp eq ptr %parent, %s
  br i1 %child, label %invalidate, label %advance
invalidate:
  call void @cpn.slot.invalidate(ptr %n)
  br label %advance
advance:
  %next = load ptr, ptr %n
  br label %scan
end:
  ret void
}

define internal void @cpn.slot.retire(ptr %s, i1 %destroy) {
  %generation = call i64 @cpn.generation(ptr %s, i1 false)
  %live = trunc i64 %generation to i1
  br i1 %live, label %begin, label %done
begin:
  %busy = getelementptr %cpn.slot, ptr %s, i32 0, i32 12
  %running = load i1, ptr %busy
  br i1 %running, label %done, label %end
end:
  store i1 true, ptr %busy
  %dp = getelementptr %cpn.slot, ptr %s, i32 0, i32 8
  %drop = load ptr, ptr %dp
  %hasdrop = icmp ne ptr %drop, null
  %run = and i1 %hasdrop, %destroy
  br i1 %run, label %call, label %invalidate
call:
  %ap = getelementptr %cpn.slot, ptr %s, i32 0, i32 3
  %addr = load ptr, ptr %ap
  call void %drop(ptr %addr)
  br label %invalidate
invalidate:
  call void @cpn.slot.invalidate(ptr %s)
  store i1 false, ptr %busy
  br label %done
done:
  ret void
}

; Root records live on their activation's stack. Free sparse child records
; only when the owning extent ends, so stale views can still be checked.
define internal void @cpn.slot.release(ptr %root) {
  br label %scan
scan:
  %link = phi ptr [@cpn.slots, %0], [%link, %unlink], [%link, %free], [%s, %keep]
  %s = load ptr, ptr %link
  %empty = icmp eq ptr %s, null
  br i1 %empty, label %done, label %test
test:
  %rp = getelementptr %cpn.slot, ptr %s, i32 0, i32 1
  %owner = load ptr, ptr %rp
  %match = icmp eq ptr %root, %owner
  br i1 %match, label %unlink, label %keep
keep:
  br label %scan
unlink:
  %next = load ptr, ptr %s
  store ptr %next, ptr %link
  %stack = icmp eq ptr %s, %root
  br i1 %stack, label %scan, label %free
free:
  call void @free(ptr %s)
  br label %scan
done:
  ret void
}

; A borrowed registration can outlive its owner's stack frame or sparse entry.
; Compare its identity against linked records before inspecting its contents.
define internal i1 @cpn.slot.linked(ptr %wanted) {
  %head = load ptr, ptr @cpn.slots
  br label %scan
scan:
  %s = phi ptr [%head,%0], [%next,%advance]
  %empty = icmp eq ptr %s, null
  br i1 %empty, label %absent, label %test
test:
  %same = icmp eq ptr %s, %wanted
  br i1 %same, label %found, label %advance
advance:
  %next = load ptr, ptr %s
  br label %scan
found:
  ret i1 true
absent:
  ret i1 false
}

define internal i1 @cpn.borrow.valid(ptr %slot, i64 %expected) {
  %raw = icmp eq ptr %slot, null
  br i1 %raw, label %valid, label %member
member:
  %linked = call i1 @cpn.slot.linked(ptr %slot)
  br i1 %linked, label %test, label %expired
test:
  %stamp = call i64 @cpn.generation(ptr %slot, i1 false)
  %original = call i64 @cpn.generation(ptr %slot, i1 true)
  %implicit = icmp eq i64 %expected, 0
  %want = select i1 %implicit, i64 %original, i64 %expected
  %same = icmp eq i64 %want, %stamp
  %alive = trunc i64 %stamp to i1
  %ok = and i1 %same, %alive
  ret i1 %ok
valid:
  ret i1 true
expired:
  ret i1 false
}

; A child extent belongs to one generation of its containing object.
define internal i1 @cpn.extent.valid(ptr %slot, i64 %extentid) {
  %linked = call i1 @cpn.slot.linked(ptr %slot)
  br i1 %linked, label %first, label %invalid
first:
  %birthid = call i64 @cpn.generation(ptr %slot, i1 true)
  %same = icmp eq i64 %birthid, %extentid
  br i1 %same, label %scan, label %invalid
scan:
  %s = phi ptr [%slot, %first], [%p, %test]
  %pp = getelementptr %cpn.slot, ptr %s, i32 0, i32 2
  %p = load ptr, ptr %pp
  %root = icmp eq ptr %p, null
  br i1 %root, label %valid, label %test
test:
  %bp = getelementptr %cpn.slot, ptr %s, i32 0, i32 11
  %birth = load i64, ptr %bp
  %actual = call i64 @cpn.generation(ptr %p, i1 false)
  %live = trunc i64 %actual to i1
  %matches = icmp eq i64 %actual, %birth
  %ok = and i1 %matches, %live
  br i1 %ok, label %scan, label %invalid
valid:
  ret i1 true
invalid:
  ret i1 false
}
