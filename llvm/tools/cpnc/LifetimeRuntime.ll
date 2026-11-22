; A complete object owns one coordinator, including its shared virtual bases.
; Each view stores its address, nominal type, base-layer drop entry, mask of
; containing layers, owner index, manual eligibility, claim and body-skip bits.
%cpn.view = type {ptr, ptr, ptr, ptr, i32, i1, i1, i1}
%cpn.boundary = type {ptr, i32, i64}
%cpn.request = type {ptr, ptr, ptr, ptr, i1}
@cpn.boundary.current = internal thread_local global ptr null
@cpn.request.pending = internal thread_local global ptr null

define internal i64 @cpn.whole.epoch() {
  %c = load ptr, ptr @cpn.boundary.current
  %active = icmp ne ptr %c, null
  br i1 %active, label %read, label %none
read:
  %location = getelementptr %cpn.boundary, ptr %c, i32 0, i32 2
  %epoch = load i64, ptr %location
  ret i64 %epoch
none:
  ret i64 0
}

define internal ptr @cpn.view.find(ptr %addr, ptr %type) {
  %boundary = load ptr, ptr @cpn.boundary.current
  %active = icmp ne ptr %boundary, null
  br i1 %active, label %init, label %missing
init:
  %views = load ptr, ptr %boundary
  %count.ptr = getelementptr %cpn.boundary, ptr %boundary, i32 0, i32 1
  %count = load i32, ptr %count.ptr
  br label %scan
scan:
  %index = phi i32 [0, %init], [%next, %advance]
  %view = getelementptr %cpn.view, ptr %views, i32 %index
  %address = load ptr, ptr %view
  %type.ptr = getelementptr %cpn.view, ptr %view, i32 0, i32 1
  %nominal = load ptr, ptr %type.ptr
  %a = icmp eq ptr %addr, %address
  %t = icmp eq ptr %type, %nominal
  %match = and i1 %a, %t
  br i1 %match, label %found, label %advance
advance:
  %next = add i32 %index, 1
  %end = icmp eq i32 %next, %count
  br i1 %end, label %missing, label %scan
found:
  ret ptr %view
missing:
  ret ptr null
}

define internal i1 @cpn.view.available(ptr %addr, ptr %type, i1 %claim) {
  %view = call ptr @cpn.view.find(ptr %addr, ptr %type)
  %missing = icmp eq ptr %view, null
  br i1 %missing, label %untracked, label %check
check:
  %flag = getelementptr %cpn.view, ptr %view, i32 0, i32 6
  %prior = load i1, ptr %flag
  %next = or i1 %prior, %claim
  store i1 %next, ptr %flag
  %live = xor i1 %prior, true
  ret i1 %live
untracked:
  ret i1 true
}

define internal i1 @cpn.view.skip(ptr %addr, ptr %type) {
  %view = call ptr @cpn.view.find(ptr %addr, ptr %type)
  %missing = icmp eq ptr %view, null
  br i1 %missing, label %untracked, label %check
check:
  %flag = getelementptr %cpn.view, ptr %view, i32 0, i32 7
  %skip = load i1, ptr %flag
  ret i1 %skip
untracked:
  ret i1 false
}

define internal i1 @cpn.whole.request(ptr %request) {
  %address = load ptr, ptr %request
  %tp = getelementptr %cpn.request, ptr %request, i32 0, i32 1
  %type = load ptr, ptr %tp
  %view = call ptr @cpn.view.find(ptr %address, ptr %type)
  %missing = icmp eq ptr %view, null
  br i1 %missing, label %outside, label %check
outside:
  ret i1 false
check:
  %c = load ptr, ptr @cpn.boundary.current
  %views = load ptr, ptr %c
  %owner.index.ptr = getelementptr %cpn.view, ptr %view, i32 0, i32 4
  %owner.index = load i32, ptr %owner.index.ptr
  %owner = getelementptr %cpn.view, ptr %views, i32 %owner.index
  %op = getelementptr %cpn.request, ptr %request, i32 0, i32 2
  %requested.owner = load ptr, ptr %op
  %otp = getelementptr %cpn.request, ptr %request, i32 0, i32 3
  %ot = load ptr, ptr %otp
  %auth = call ptr @cpn.view.find(ptr %requested.owner, ptr %ot)
  %owned = icmp eq ptr %auth, %owner
  %permitted.ptr = getelementptr %cpn.view, ptr %view, i32 0, i32 5
  %permitted = load i1, ptr %permitted.ptr
  %legal = and i1 %owned, %permitted
  %available = call i1 @cpn.view.available(ptr %address, ptr %type, i1 false)
  %ok = and i1 %legal, %available
  br i1 %ok, label %begin, label %invalid
invalid:
  call void @llvm.trap()
  unreachable
begin:
  %taken = call i1 @cpn.view.available(ptr %address, ptr %type, i1 true)
  %ep = getelementptr %cpn.boundary, ptr %c, i32 0, i32 2
  %epoch = load i64, ptr %ep
  %new = add i64 %epoch, 1
  store i64 %new, ptr %ep
  %mask.ptr = getelementptr %cpn.view, ptr %view, i32 0, i32 3
  %mask = load ptr, ptr %mask.ptr
  %len.ptr = getelementptr %cpn.boundary, ptr %c, i32 0, i32 1
  %len = load i32, ptr %len.ptr
  br label %scan
scan:
  %i = phi i32 [0, %begin], [%next, %advance]
  %bit.ptr = getelementptr i8, ptr %mask, i32 %i
  %bit = load i8, ptr %bit.ptr
  %ancestor = icmp ne i8 %bit, 0
  br i1 %ancestor, label %omit, label %advance
omit:
  %flag = getelementptr %cpn.view, ptr %views, i32 %i, i32 7
  store i1 true, ptr %flag
  br label %advance
advance:
  %next = add i32 %i, 1
  %end = icmp eq i32 %next, %len
  br i1 %end, label %attempt, label %scan
attempt:
  %dp = getelementptr %cpn.request, ptr %request, i32 0, i32 4
  %destroy = load i1, ptr %dp
  br i1 %destroy, label %run, label %done
run:
  %fp = getelementptr %cpn.view, ptr %view, i32 0, i32 2
  %drop = load ptr, ptr %fp
  call void %drop(ptr %address)
  br label %done
done:
  ret i1 true
}

; Transfers attach to the complete storage generation. The caller has
; established the nominal virtual-base relation before entering these helpers.
%cpn.owner = type {ptr, ptr, ptr, ptr, ptr, ptr}
@cpn.owners = internal thread_local global ptr null

define internal ptr @cpn.slot.enclosing(ptr %view, ptr %virtual) {
  %first = load ptr, ptr @cpn.slots
  br label %scan
scan:
  %s = phi ptr [%first, %0], [%next, %item]
  %best = phi ptr [null, %0], [%chosen, %item]
  %limit = phi i64 [-1, %0], [%size.limit, %item]
  %end = icmp eq ptr %s, null
  br i1 %end, label %done, label %item
item:
  %next = load ptr, ptr %s
  %address.ptr = getelementptr %cpn.slot, ptr %s, i32 0, i32 3
  %address = load ptr, ptr %address.ptr
  %size.ptr = getelementptr %cpn.slot, ptr %s, i32 0, i32 9
  %size = load i64, ptr %size.ptr
  %base = ptrtoint ptr %address to i64
  %a = ptrtoint ptr %view to i64
  %v = ptrtoint ptr %virtual to i64
  %da = sub i64 %a, %base
  %dv = sub i64 %v, %base
  %inside.a = icmp ult i64 %da, %size
  %inside.v = icmp ult i64 %dv, %size
  %contains = and i1 %inside.a, %inside.v
  %narrower = icmp ult i64 %size, %limit
  %better = and i1 %contains, %narrower
  %stamp = call i64 @cpn.generation(ptr %s, i1 false)
  %alive = trunc i64 %stamp to i1
  %eligible = and i1 %alive, %better
  %chosen = select i1 %eligible, ptr %s, ptr %best
  %size.limit = select i1 %eligible, i64 %size, i64 %limit
  br label %scan
done:
  ret ptr %best
}

define internal ptr @cpn.owner.find(ptr %slot, ptr %base, ptr %type) {
  %head = load ptr, ptr @cpn.owners
  br label %scan
scan:
  %item = phi ptr [%head, %0], [%next, %advance]
  %empty = icmp eq ptr %item, null
  br i1 %empty, label %done, label %test
test:
  %sp = getelementptr %cpn.owner, ptr %item, i32 0, i32 1
  %registered = load ptr, ptr %sp
  %bp = getelementptr %cpn.owner, ptr %item, i32 0, i32 2
  %address = load ptr, ptr %bp
  %tp = getelementptr %cpn.owner, ptr %item, i32 0, i32 3
  %nominal = load ptr, ptr %tp
  %s = icmp eq ptr %slot, %registered
  %b = icmp eq ptr %base, %address
  %t = icmp eq ptr %type, %nominal
  %sb = and i1 %s, %b
  %match = and i1 %sb, %t
  br i1 %match, label %done, label %advance
advance:
  %next = load ptr, ptr %item
  br label %scan
done:
  ret ptr %item
}

define internal void @cpn.owner.assign(ptr %slot, ptr %base, ptr %type, ptr %target, ptr %target.type) {
  %prior = call ptr @cpn.owner.find(ptr %slot, ptr %base, ptr %type)
  %absent = icmp eq ptr %prior, null
  br i1 %absent, label %allocate, label %store
allocate:
  %mem = call ptr @malloc(i64 ptrtoint (ptr getelementptr (%cpn.owner, ptr null, i32 1) to i64))
  %oom = icmp eq ptr %mem, null
  br i1 %oom, label %failed, label %link
failed:
  call void @llvm.trap()
  unreachable
link:
  %head = load ptr, ptr @cpn.owners
  store ptr %head, ptr %mem
  %sp = getelementptr %cpn.owner, ptr %mem, i32 0, i32 1
  store ptr %slot, ptr %sp
  %bp = getelementptr %cpn.owner, ptr %mem, i32 0, i32 2
  store ptr %base, ptr %bp
  %tp = getelementptr %cpn.owner, ptr %mem, i32 0, i32 3
  store ptr %type, ptr %tp
  store ptr %mem, ptr @cpn.owners
  br label %store
store:
  %item = phi ptr [%prior, %0], [%mem, %link]
  %target.ptr = getelementptr %cpn.owner, ptr %item, i32 0, i32 4
  store ptr %target, ptr %target.ptr
  %type.ptr = getelementptr %cpn.owner, ptr %item, i32 0, i32 5
  store ptr %target.type, ptr %type.ptr
  ret void
}

define internal i1 @cpn.owner.matches(ptr %item, ptr %target, ptr %type) {
  %absent = icmp eq ptr %item, null
  br i1 %absent, label %none, label %test
none:
  ret i1 false
test:
  %ap = getelementptr %cpn.owner, ptr %item, i32 0, i32 4
  %a = load ptr, ptr %ap
  %tp = getelementptr %cpn.owner, ptr %item, i32 0, i32 5
  %t = load ptr, ptr %tp
  %address = icmp eq ptr %a, %target
  %nominal = icmp eq ptr %t, %type
  %both = and i1 %address, %nominal
  ret i1 %both
}

define internal void @cpn.owner.forget(ptr %slot) {
  br label %scan
scan:
  %link = phi ptr [@cpn.owners, %0], [%link, %unlink], [%item, %keep]
  %item = load ptr, ptr %link
  %empty = icmp eq ptr %item, null
  br i1 %empty, label %done, label %test
test:
  %sp = getelementptr %cpn.owner, ptr %item, i32 0, i32 1
  %registered = load ptr, ptr %sp
  %same = icmp eq ptr %slot, %registered
  br i1 %same, label %unlink, label %keep
unlink:
  %next = load ptr, ptr %item
  store ptr %next, ptr %link
  call void @free(ptr %item)
  br label %scan
keep:
  br label %scan
done:
  ret void
}
