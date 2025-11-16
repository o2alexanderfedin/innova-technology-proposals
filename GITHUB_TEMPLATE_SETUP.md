# GitHub Template Repository Setup

**Issue**: "Use this template" button not visible or not working

**Solution**: Enable the Template Repository setting in GitHub (via CLI or Web UI)

---

## Quick CLI Solution (Recommended)

For repository owners who prefer command-line tools:

```bash
# Authenticate with GitHub (if not already)
gh auth login

# Enable template repository for your repo
gh api -X PATCH /repos/OWNER/REPO \
  -F is_template=true

# Example for this repository:
gh api -X PATCH /repos/o2alexanderfedin/strategic-research-automation-template \
  -F is_template=true
```

**Verification**:
```bash
# Check if template is enabled
gh api /repos/o2alexanderfedin/strategic-research-automation-template \
  --jq '.is_template'
# Should return: true
```

**Benefits of CLI approach**:
- ✅ Instant (no UI navigation)
- ✅ Scriptable for automation
- ✅ Works remotely without browser
- ✅ Can be integrated into repository setup scripts

---

## How to Enable Template Repository (Web UI Alternative)

### For Repository Owners

1. **Navigate to your repository on GitHub**:
   ```
   https://github.com/o2alexanderfedin/strategic-research-automation-template
   ```

2. **Click on "Settings"** (top navigation bar)

3. **Scroll down to "Template repository" section** (near the top of the Settings page, under "General")

4. **Check the box** ✅ **"Template repository"**

   ![Template Repository Checkbox](https://docs.github.com/assets/cb-27121/images/help/repository/template-repository-checkbox.png)

5. **The "Use this template" button will now appear** on the repository main page (green button, top right)

---

## Verification

### After Enabling Template Repository

Visit your repository main page:
```
https://github.com/o2alexanderfedin/strategic-research-automation-template
```

You should see:
- ✅ A green **"Use this template"** button (next to "Code" button)
- ✅ Badge shows "Template" under the repository name

### What Users Will See

When visiting the template repository, users will see:

```
┌────────────────────────────────────────────────────┐
│  o2alexanderfedin / strategic-research-automation  │
│  Template                                          │
│                                                    │
│  [★ Star]  [Code ▼]  [Use this template ▼]       │
└────────────────────────────────────────────────────┘
```

---

## Using the Template

### For Users Creating New Projects

1. **Click "Use this template"** button
2. **Select "Create a new repository"**
3. **Configure your new repository**:
   - Repository name: `my-research-project`
   - Description: "Strategic research for [your project]"
   - Visibility: Private (recommended for proprietary research)
   - ✅ Include all branches (optional - usually NOT needed)

4. **Click "Create repository from template"**

5. **Clone your new repository**:
   ```bash
   git clone https://github.com/YOUR-USERNAME/my-research-project
   cd my-research-project
   ```

6. **Run setup**:
   ```bash
   ./scripts/setup-template.sh
   ```

---

## Differences: Template vs. Fork

| Feature | Template | Fork |
|---------|----------|------|
| **Git History** | ✅ Clean (no original history) | ❌ Full original history |
| **Upstream Link** | ❌ No connection | ✅ Linked to original |
| **Use Case** | Starting new projects | Contributing back |
| **Pull Requests** | ❌ Cannot PR to template | ✅ Can PR to original |
| **Independence** | ✅ Fully independent | ❌ Tied to original |

**For this template**: Use **"Use this template"**, NOT fork.

---

## Troubleshooting

### "Use this template" button not visible

**Cause**: Template repository setting not enabled

**Solution**:
1. Repository owner must enable template setting (see above)
2. Refresh the page
3. The button should appear next to "Code" button

### "Use this template" button disabled/greyed out

**Cause**: You're viewing your own template repository

**Solution**:
- You cannot use template on your own repository
- Clone it normally or create a new repository manually:
  ```bash
  git clone https://github.com/o2alexanderfedin/strategic-research-automation-template my-project
  cd my-project
  rm -rf .git
  git init
  ```

### Button exists but clicking does nothing

**Cause**: Rare UI bug (display: none CSS issue)

**Solution**:
1. Hard refresh: Ctrl+Shift+R (Windows/Linux) or Cmd+Shift+R (Mac)
2. Try different browser
3. Clear browser cache
4. Use GitHub CLI as workaround:
   ```bash
   gh repo create my-project --template o2alexanderfedin/strategic-research-automation-template --private
   ```

---

## GitHub CLI Alternative

For power users who prefer command line:

```bash
# Install GitHub CLI (if not already installed)
# macOS
brew install gh

# Ubuntu/Debian
sudo apt install gh

# Authenticate
gh auth login

# Create repository from template
gh repo create my-research-project \
  --template o2alexanderfedin/strategic-research-automation-template \
  --private \
  --clone

# Navigate and setup
cd my-research-project
./scripts/setup-template.sh
```

**Benefits**:
- ✅ Faster than web UI
- ✅ Scriptable for automation
- ✅ Works even if web UI has issues
- ✅ Can be integrated into setup scripts

---

## Template Repository Best Practices

### For Template Maintainers

1. **Enable template setting** ✅ (see above)

2. **Add template badge** to README.md:
   ```markdown
   [![GitHub Template](https://img.shields.io/badge/template-Use%20this%20template-brightgreen)](https://github.com/o2alexanderfedin/strategic-research-automation-template/generate)
   ```

3. **Create `.github/TEMPLATE_README.md`** (optional):
   - This file replaces README.md when template is used
   - Useful for removing template-specific content

4. **Use template variables** in files (optional):
   - `{{PROJECT_NAME}}`
   - `{{COMPANY_NAME}}`
   - Replaced during repository creation

5. **Test the template**:
   - Ask someone else to test "Use this template"
   - Verify setup scripts work in fresh repository
   - Check all files copy correctly

### For Template Users

1. **Use "Use this template"**, not fork
2. **Make repository private** for proprietary research
3. **Run setup script immediately** after creation
4. **Customize for your needs** (context files, config)
5. **Remove template-specific files** if needed

---

## Verification Checklist

Before sharing template with users:

- [ ] Template repository checkbox enabled in Settings
- [ ] "Use this template" button visible on main page
- [ ] Template badge in README.md works
- [ ] Tested creating repository from template
- [ ] Setup script (`./scripts/setup-template.sh`) works in fresh clone
- [ ] All necessary files included
- [ ] No sensitive data in template (API keys, etc.)
- [ ] Documentation mentions "Use this template"
- [ ] TEMPLATE_STRATEGY.md explains template usage

---

## References

- [GitHub Docs: Creating a template repository](https://docs.github.com/en/repositories/creating-and-managing-repositories/creating-a-template-repository)
- [GitHub Docs: Creating a repository from a template](https://docs.github.com/en/repositories/creating-and-managing-repositories/creating-a-repository-from-a-template)
- [GitHub CLI: gh repo create](https://cli.github.com/manual/gh_repo_create)

---

## Quick Summary

**Problem**: "Use this template" button not working

**Solution** (for repository owner):
1. Go to repository Settings
2. Enable "Template repository" checkbox
3. Button will appear immediately

**For users**: Click green "Use this template" button → Create new repository

---

**Last Updated**: 2025-11-14
**Repository**: https://github.com/o2alexanderfedin/strategic-research-automation-template
